/* 
 * slaDaemon.c - Daemon to collect snapshots of slab info.
 *
 * Based on slabtop.c 
 * Chris Rivera <cmrivera@ufl.edu>
 * Robert Love <rml@tech9.net>
 *
 * New version
 * Javier Alonso <javier.alonso@duke.edu>
 *
 * This program is licensed under the GNU Library General Public License, v2
 *
 * This daemon collects the slab active objects and total active memory consumed by each slab cache of the kernel
 * from the beginning of the execution. Moreover, it can be configured to collect just the last 15 minutes and last hour of 
 * execution. Then, it performs MannKendall Trend test with tied values correction for these three time series for each
 * slab cache of the system. Then, it indicates which ones present an monotonic increasing memory usage. 
 *
 * Pending TODO: 
 * 1) Implement the Mannkendall correction for autocorrelation: There are two possible implementations:
 * 1.a) Modified Mann-Kendall Test which is robust in the presence of autocorrelation based on a modified variance of S.
 * 1.b) Mann-Kendall test with Pre-whitening is based on first remove the serial correlation
 * Ref--> The Yamuna River Basin: Water Resources and Environment> Alka Upadhyay, C. Chekhar, P. Ojha, Vijay P. Singh. 
 *
 * 2) Implement a modified version of slabtop to plot not only current stats but also the stats computed by this daemon. 
 * Copyright (C) 2015 Javier Alonso
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <signal.h>
#include <getopt.h>
#include <ctype.h>
#include <syslog.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <math.h>

#include <sys/select.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

#include "proc/slab.h"
#include "proc/version.h"



#define DAEMON_NAME			"slabdaemon"
#define DEF_SORT_FUNC		sort_nr_active_objs
#define SLAB_STAT_ZERO		{ nr_objs: 0 }
#define MID_TERM 			3600
#define SHORT_TERM			900


struct s{
	struct s *next;
	struct s *prev;
	double timestamp;
	double value;
};
struct slab_MK{
	char name[SLAB_INFO_NAME_LEN];  /* name of this cache */
	struct slab_MK *next;
	struct s *sValues;
	struct s *lastMID_TERM; //pointer to the last slab_value of the last MID_TERM.
	struct s *lastSHORT_TERM; //pointer to the last slab_value of the last half MID_TERM.
	struct slab_buckets *tiedbucketsTotal;
	struct slab_buckets *tiedbucketsMID_TERM;
	struct slab_buckets *tiedbucketsSHORT_TERM;
};

struct slab_buckets{
	 struct slab_buckets *next;
	 double value;
	 int tied;
};

static long delay = 30;
static double criticalValue=1.96;
static struct slab_MK *slab_mk_values;
static int (*sort_func)(const struct slab_info *, const struct slab_info *);


static struct slab_info *merge_objs(struct slab_info *a, struct slab_info *b)
{
	struct slab_info sorted_list;
	struct slab_info *curr = &sorted_list;

	while ((a != NULL) && (b != NULL)) {
		if (sort_func(a, b)) {
			curr->next = a;
			curr = a;
			a = a->next;
		} else {
			curr->next = b;
			curr = b;
			b = b->next;
		}
	}

	curr->next = (a == NULL) ? b : a;
	return sorted_list.next;
}

/* 
 * slabsort - merge sort the slab_info linked list based on sort_func
 */
static struct slab_info *slabsort(struct slab_info *list)
{
	struct slab_info *a, *b;

	if ((list == NULL) || (list->next == NULL))
		return list;

	a = list;
	b = list->next;

	while ((b != NULL) && (b->next != NULL)) {
		list = list->next;
		b = b->next->next;
	}
	
	b = list->next;
	list->next = NULL;

	return merge_objs(slabsort(a), slabsort(b));
}

/*
 * Sort Routines.  Each of these should be associated with a command-line
 * search option.  The functions should fit the prototype:
 *
 *	int sort_foo(const struct slab_info *a, const struct slab_info *b)
 *
 * They return one if the first parameter is larger than the second
 * Otherwise, they return zero.
 */

static int sort_name(const struct slab_info *a, const struct slab_info *b)
{
	return (strcmp(a->name, b->name) < 0) ? 1 : 0;
}

static int sort_nr_active_objs(const struct slab_info *a,
				const struct slab_info *b)
{
	return (a->nr_active_objs > b->nr_active_objs);
}

static int sort_obj_size(const struct slab_info *a, const struct slab_info *b)
{
	return (a->obj_size > b->obj_size);
}



static void usage(const char *cmd)
{
	fprintf(stderr, "usage: %s [options]\n\n", cmd);
	fprintf(stderr, "options:\n");
	fprintf(stderr, "  --delay=n, -d n    "
		"delay n seconds between updates\n");
	fprintf(stderr, "  --sort=S, -s S     "
		"specify sort criteria S (see below)\n");
	fprintf(stderr, "  --help             display this help and exit\n\n");
	fprintf(stderr, "The following are valid sort criteria:\n");
	fprintf(stderr, "  a: sort by number of active objects\n");
	fprintf(stderr, "  n: sort by name\n");
	fprintf(stderr, "  s: sort by object size\n");
}

/*
 * set_sort_func - return the slab_sort_func that matches the given key.
 * On unrecognizable key, DEF_SORT_FUNC is returned.
 */
static void * set_sort_func(char key)
{
	switch (key) {
	case 'n':
		return sort_name;
	case 'a':
		return sort_nr_active_objs;
	case 's':
		return sort_obj_size;
	default:
		return DEF_SORT_FUNC;
	}
}

static struct slab_MK * searchSLAB(struct slab_MK *s_mk_v, char* name){
	int found=0;
	struct slab_MK *curr;
	curr=s_mk_v;
	while((curr) && !found){
		if (strcmp(curr->name,name)==0){
			found=1;		
		}else{
			curr=curr->next;
		}
	}
	return curr;
}

static struct slab_buckets * searchBucket(struct slab_buckets *buckets,double value){
	int found=0;
	struct slab_buckets *curr;
	curr=buckets;
	while (curr && !found){
		if(value==curr->value){
			found=1;
		}else{
			curr=curr->next;
		}
	}
	return curr;
}



static int monitor(int timestamp,struct slab_info *slab_list,FILE *fp)
{
	struct s *actual_slab_value=NULL;
	struct slab_MK *actual_slab_MK=NULL;
	struct s *actualS=NULL;
	struct s *actual=NULL;
	struct slab_buckets *actual_slab_bucket=NULL;
	struct slab_buckets *tiedbucketTotal;
	struct slab_buckets *tiedbucketMID_TERM;
	struct slab_buckets *tiedbucketSHORT_TERM;
	int accumTotal=0, accumMID_TERM=0, accumSHORT_TERM=0;
	char *trendTotal=NULL;
	char *trendMID_TERM=NULL;
	char *trendSHORT_TERM=NULL;
	long int counterTotal=0, counterMID_TERM=0, counterSHORT_TERM=0;
	double varSTotal=0.0;
	double varSMID_TERM=0.0;
	double varSSHORT_TERM=0.0;
	long double firstPartVarianceTotal=0;
	long double firstPartVarianceMID_TERM=0;
	long double firstPartVarianceSHORT_TERM=0;
	long double secondPartVarianceTotal=0.0;
	long double secondPartVarianceMID_TERM=0.0;
	long double secondPartVarianceSHORT_TERM=0.0;
	double zTotal=0.0;
	double zMID_TERM=0.0;
	double zSHORT_TERM=0.0;
	struct slab_info *curr=NULL;
	struct slab_stat stats = SLAB_STAT_ZERO;
	syslog(LOG_NOTICE, "get slabinfo Active/Total Objects");
	if (get_slabinfo(&slab_list, &stats)){
		syslog(LOG_NOTICE, "ERROR GET SLAB INFO DATA RETRIVAL");
		return 1;
	}
	slab_list = slabsort(slab_list);
	curr = slab_list;
		while (curr) {
//		if(strcmp(curr->name,"kmalloc-256")==0 || strcmp(curr->name,"kmalloc-32")==0){
			syslog(LOG_NOTICE, "slab ID0: TIMESTAMP -1: %-23s",curr->name);
			syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 0: ");
			actual_slab_MK=NULL;
			actual_slab_MK = searchSLAB(slab_mk_values,curr->name);
			if (!actual_slab_MK){ //initialize the temporal ML values for tests
					syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 1: ");
					actual_slab_value= malloc(sizeof(struct s));
					actual_slab_value->value=curr->nr_active_objs*curr->obj_size;
					actual_slab_value->next=NULL;
					actual_slab_value->prev=NULL;
					actual_slab_value->timestamp=timestamp;
					actual_slab_bucket = malloc(sizeof(struct slab_buckets));
					actual_slab_bucket->value=actual_slab_value->value;
					actual_slab_bucket->tied=1;
					actual_slab_bucket->next=NULL;
					actual_slab_MK = malloc(sizeof(struct slab_MK));
					strcpy(actual_slab_MK->name,curr->name);
					actual_slab_MK->lastMID_TERM = actual_slab_value;
					actual_slab_MK->lastSHORT_TERM = actual_slab_value;
					actual_slab_MK->sValues=actual_slab_value;
					actual_slab_MK->tiedbucketsTotal=actual_slab_bucket;
					actual_slab_bucket = malloc(sizeof(struct slab_buckets));
					actual_slab_bucket->value=actual_slab_value->value;
					actual_slab_bucket->tied=1;
					actual_slab_bucket->next=NULL;
					actual_slab_MK->tiedbucketsMID_TERM=actual_slab_bucket;
					actual_slab_bucket = malloc(sizeof(struct slab_buckets));
					actual_slab_bucket->value=actual_slab_value->value;
					actual_slab_bucket->tied=1;
					actual_slab_bucket->next=NULL;
					actual_slab_MK->tiedbucketsSHORT_TERM=actual_slab_bucket;
					actual_slab_MK->next=slab_mk_values;
					slab_mk_values=actual_slab_MK;
					syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 2: %d;%d;%lf",curr->obj_size,curr->nr_active_objs,actual_slab_value->value);
			}else{
				// CLEAN MID_TERM AND SHORT_TERM STRUCTURES IF NEEDED
				if (timestamp-MID_TERM>actual_slab_MK->lastMID_TERM->timestamp)
				{
					tiedbucketMID_TERM=searchBucket(actual_slab_MK->tiedbucketsMID_TERM,actual_slab_MK->lastMID_TERM->value);
					if(tiedbucketMID_TERM){
						tiedbucketMID_TERM->tied-=1;
					}
					actual_slab_MK->lastMID_TERM=actual_slab_MK->lastMID_TERM->prev;
				}
				if (timestamp-SHORT_TERM>actual_slab_MK->lastSHORT_TERM->timestamp){
					tiedbucketSHORT_TERM=searchBucket(actual_slab_MK->tiedbucketsSHORT_TERM,actual_slab_MK->lastSHORT_TERM->value);
					if(tiedbucketSHORT_TERM){
						tiedbucketSHORT_TERM->tied-=1;
					}
					actual_slab_MK->lastSHORT_TERM=actual_slab_MK->lastSHORT_TERM->prev;
				}
				syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 3.0: ");
				syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 3.1: ");
				actual_slab_value= malloc(sizeof(struct s));
				actual_slab_value->value=curr->nr_active_objs*curr->obj_size;
				actual_slab_value->timestamp=timestamp;
				actual_slab_value->next=NULL;
				actual_slab_value->prev=NULL;
				tiedbucketTotal= searchBucket(actual_slab_MK->tiedbucketsTotal,actual_slab_value->value);
				tiedbucketMID_TERM= searchBucket(actual_slab_MK->tiedbucketsMID_TERM,actual_slab_value->value);
				tiedbucketSHORT_TERM= searchBucket(actual_slab_MK->tiedbucketsSHORT_TERM,actual_slab_value->value);
				if (tiedbucketTotal){
					tiedbucketTotal->tied+=1;
				}else{
					actual_slab_bucket = malloc(sizeof(struct slab_buckets));
					actual_slab_bucket->value=actual_slab_value->value;
					actual_slab_bucket->tied=1;
					actual_slab_bucket->next=NULL;
					actual_slab_bucket->next=actual_slab_MK->tiedbucketsTotal;
					actual_slab_MK->tiedbucketsTotal=actual_slab_bucket;
				}
				if (tiedbucketMID_TERM){
					tiedbucketMID_TERM->tied+=1;
				}else{
					actual_slab_bucket = malloc(sizeof(struct slab_buckets));
					actual_slab_bucket->value=actual_slab_value->value;
					actual_slab_bucket->tied=1;
					actual_slab_bucket->next=NULL;
					actual_slab_bucket->next=actual_slab_MK->tiedbucketsMID_TERM;
					actual_slab_MK->tiedbucketsMID_TERM=actual_slab_bucket;
				}
				if (tiedbucketSHORT_TERM){
					tiedbucketSHORT_TERM->tied+=1;
				}else{
					actual_slab_bucket = malloc(sizeof(struct slab_buckets));
					actual_slab_bucket->value=actual_slab_value->value;
					actual_slab_bucket->tied=1;
					actual_slab_bucket->next=NULL;
					actual_slab_bucket->next=actual_slab_MK->tiedbucketsSHORT_TERM;
					actual_slab_MK->tiedbucketsSHORT_TERM=actual_slab_bucket;
				}
				actual_slab_MK->sValues->prev=actual_slab_value;
				actual_slab_value->next=actual_slab_MK->sValues;
				actual_slab_MK->sValues=actual_slab_value;
				syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 4: %d;%d;%lf",curr->obj_size,curr->nr_active_objs,actual_slab_value->value);
				}
			syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 5:");
			actualS=actual_slab_MK->sValues;
			syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 5.1:");
			actual=actual_slab_MK->sValues;
			accumTotal=0;
			accumMID_TERM=0;
			accumSHORT_TERM=0;
			varSTotal=0.0;
			varSMID_TERM=0.0;
			varSSHORT_TERM=0.0;
			zTotal=0.0;
			zMID_TERM=0.0;
			zSHORT_TERM=0.0;
			syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 5.2:");
			counterTotal=0;
			counterMID_TERM=0;
			counterSHORT_TERM=0;
			while (actualS){ 
					syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 6:");
					actual=actualS->next;
					while(actual){
						if(actualS->value > actual->value){
							if(actualS->timestamp>=(timestamp-MID_TERM) && actual->timestamp>=(timestamp-MID_TERM)){
								accumMID_TERM+=1;
							}
							if(actualS->timestamp>=(timestamp-SHORT_TERM) && actual->timestamp>=(timestamp-SHORT_TERM) ){
								accumSHORT_TERM+=1;
							}
							accumTotal+=1;
						}else if(actualS->value < actual->value) {
							accumTotal-=1;
							if(actualS->timestamp>=(timestamp-MID_TERM) && actual->timestamp>=(timestamp-MID_TERM)){
								accumMID_TERM-=1;
							}
							if(actualS->timestamp>=(timestamp-SHORT_TERM) && actual->timestamp>=(timestamp-SHORT_TERM) ){
								accumSHORT_TERM-=1;
							}
						}
						actual=actual->next;
					}
					counterTotal+=1;
					if(actualS->timestamp>=(timestamp-MID_TERM)){
						counterMID_TERM+=1;
					}
					if(actualS->timestamp>=(timestamp-SHORT_TERM)){
						counterSHORT_TERM+=1;
					}
					actualS=actualS->next;
			}
			syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 6.1:");

			secondPartVarianceTotal=0.0;
			tiedbucketTotal=actual_slab_MK->tiedbucketsTotal;
			while(tiedbucketTotal){
				syslog(LOG_NOTICE, "slab TIMESTAMP 6.2-Total: %f;%d",tiedbucketTotal->value,tiedbucketTotal->tied);
				if(tiedbucketTotal->tied>1){
					secondPartVarianceTotal+=(tiedbucketTotal->tied*(tiedbucketTotal->tied-1)*(2*tiedbucketTotal->tied+5));
				}
				tiedbucketTotal=tiedbucketTotal->next;
			}
			secondPartVarianceMID_TERM=0.0;
			tiedbucketMID_TERM=actual_slab_MK->tiedbucketsMID_TERM;
			while(tiedbucketMID_TERM){
				syslog(LOG_NOTICE, "slab TIMESTAMP 6.2-MID_TERM: %f;%d",tiedbucketMID_TERM->value,tiedbucketMID_TERM->tied);
				if(tiedbucketMID_TERM->tied>1){
					secondPartVarianceMID_TERM+=(tiedbucketMID_TERM->tied*(tiedbucketMID_TERM->tied-1)*(2*tiedbucketMID_TERM->tied+5));
				}
				tiedbucketMID_TERM=tiedbucketMID_TERM->next;
			}
			secondPartVarianceSHORT_TERM=0.0;
			tiedbucketSHORT_TERM=actual_slab_MK->tiedbucketsSHORT_TERM;
			while(tiedbucketSHORT_TERM){
				syslog(LOG_NOTICE, "slab TIMESTAMP 6.2-SHORT_TERM: %f;%d",tiedbucketSHORT_TERM->value,tiedbucketSHORT_TERM->tied);
				if(tiedbucketSHORT_TERM->tied>1){
					secondPartVarianceSHORT_TERM+=(tiedbucketSHORT_TERM->tied*(tiedbucketSHORT_TERM->tied-1)*(2*tiedbucketSHORT_TERM->tied+5));
				}
				tiedbucketSHORT_TERM=tiedbucketSHORT_TERM->next;
			}
			firstPartVarianceTotal=0;
			if (counterTotal>1){
				firstPartVarianceTotal=(counterTotal*(counterTotal-1)*(2*counterTotal+5));
				varSTotal = (firstPartVarianceTotal-secondPartVarianceTotal)/18; //this needs to be confirmed. 
				syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 7.3 MID_TERM: %f;%Le;%Le",varSTotal,firstPartVarianceTotal,secondPartVarianceTotal);
				if (accumTotal<0){
					zTotal=(accumTotal+1)/sqrt(varSTotal);
				}else if(accumTotal>0){zTotal=(accumTotal-1)/sqrt(varSTotal);}
				else{zTotal=0;}
			}
			trendTotal=malloc(sizeof(char*));;
			if (fabs(zTotal)>criticalValue){
					syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 7.1:");
					if (zTotal>0){
						strcpy(trendTotal,"YES");
					}
					else{strcpy(trendTotal,"NO");}
			}
			else{syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 7.2:");strcpy(trendTotal,"NO");}
			firstPartVarianceMID_TERM=0;
			if (counterMID_TERM>1){
				firstPartVarianceMID_TERM=(counterMID_TERM*(counterMID_TERM-1)*(2*counterMID_TERM+5));
				varSMID_TERM = (firstPartVarianceMID_TERM-secondPartVarianceMID_TERM)/18; //this needs to be confirmed. 
				syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 7.3 MID_TERM: %f;%Le;%Le",varSMID_TERM,firstPartVarianceMID_TERM,secondPartVarianceMID_TERM);
				if (accumMID_TERM<0){
					zMID_TERM=(accumMID_TERM+1)/sqrt(varSMID_TERM);
				}else if(accumMID_TERM>0){zMID_TERM=(accumMID_TERM-1)/sqrt(varSMID_TERM);}
				else{zMID_TERM=0;}
			}
			trendMID_TERM=malloc(sizeof(char*));;
			if (fabs(zMID_TERM)>criticalValue){
					syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 7.1:");
					if (zMID_TERM>0){
						strcpy(trendMID_TERM,"YES");
					}
					else{strcpy(trendMID_TERM,"NO");}
			}
			else{syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 7.2:");strcpy(trendMID_TERM,"NO");}
			firstPartVarianceSHORT_TERM=0;
			if (counterSHORT_TERM>1){
				firstPartVarianceSHORT_TERM=(counterSHORT_TERM*(counterSHORT_TERM-1)*(2*counterSHORT_TERM+5));
				varSSHORT_TERM = (firstPartVarianceSHORT_TERM-secondPartVarianceSHORT_TERM)/18;  
				syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 7.3 MID_TERM: %f;%Le;%Le",varSSHORT_TERM,firstPartVarianceSHORT_TERM,secondPartVarianceSHORT_TERM);
				if (accumSHORT_TERM<0){
					zSHORT_TERM=(accumSHORT_TERM+1)/sqrt(varSSHORT_TERM);
				}else if(accumSHORT_TERM>0){zSHORT_TERM=(accumSHORT_TERM-1)/sqrt(varSSHORT_TERM);}
				else{zSHORT_TERM=0;}
			}
			trendSHORT_TERM=malloc(sizeof(char*));;
			if (fabs(zSHORT_TERM)>criticalValue){
					syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 7.1:");
					if (zSHORT_TERM>0){
						strcpy(trendSHORT_TERM,"YES");
					}
					else{strcpy(trendSHORT_TERM,"NO");}
			}
			else{syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 7.2:");strcpy(trendSHORT_TERM,"NO");}
			syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 7.3:");
			syslog(LOG_NOTICE,"slab: %d;%6u;%6u;%-23s;%d;%ld;%f;%-10s;%d;%ld;%f;%-10s;%d;%ld;%f;%-10s",timestamp,
			curr->nr_active_objs, curr->obj_size, curr->name,accumTotal,counterTotal,
			zTotal,trendTotal,accumMID_TERM,counterMID_TERM,zMID_TERM,trendMID_TERM,accumSHORT_TERM,
			counterSHORT_TERM,zSHORT_TERM,trendSHORT_TERM);
			
			fprintf(fp,"%d;%6u;%6u;%-23s;%d;%ld;%f;%Le;%Le;%f;%-10s;%d;%ld;%f;%Le;%Le;%f;%-10s;%d;%ld;%f;%Le;%Le;%f;%-10s\n",timestamp,
			curr->nr_active_objs, curr->obj_size, curr->name,accumTotal,counterTotal,varSTotal,firstPartVarianceTotal,secondPartVarianceTotal,
			zTotal,trendTotal,accumMID_TERM,counterMID_TERM,varSMID_TERM,firstPartVarianceMID_TERM,secondPartVarianceMID_TERM,zMID_TERM,trendMID_TERM,accumSHORT_TERM,
			counterSHORT_TERM,varSSHORT_TERM,firstPartVarianceSHORT_TERM,secondPartVarianceSHORT_TERM,zSHORT_TERM,trendSHORT_TERM);
			syslog(LOG_NOTICE, "slab ID0: TIMESTAMP 8:");
	//		}
			curr = curr->next;
		}		
		free(trendTotal);
		free(trendMID_TERM);
		free(trendSHORT_TERM);
		put_slabinfo(slab_list);
	return 0;
}



int main(int argc, char *argv[])
{
	int op;
	pid_t pid, sid;
	struct slab_info *slab_list = NULL;
	FILE *fp= NULL;
	int i=0;
	
	struct option longopts[] = {
		{ "delay",	1, NULL, 'd' },
		{ "sort",	1, NULL, 's' },
		{ "help",	0, NULL, 'h' },
		{  NULL,	0, NULL, 0 }
	};

	sort_func = DEF_SORT_FUNC;

	while ((op = getopt_long(argc, argv, "d:s:h", longopts, NULL)) != -1) {
		int ret = 1;

		switch (op) {
		case 'd':
			errno = 0;
			delay = strtol(optarg, NULL, 10);
			if (errno) {
				perror("strtoul");
				return 1;
			}
			if (delay < 0) {
				fprintf(stderr, "error: can't have a "\
					"negative delay\n");
				exit(1);
			}
			break;
		case 's':
			sort_func = set_sort_func(optarg[0]);
			break;
		case 'h':
			ret = 0;
		default:
			usage(argv[0]);
			return ret;
		}
	}
	//initialize the syslog
	setlogmask(LOG_UPTO (LOG_NOTICE));
	openlog("testDaemon", LOG_CONS | LOG_PID | LOG_NDELAY, LOG_LOCAL1);
	

	pid = fork();
	
	if (pid<0){ return -1;}
	
	if (pid>0) {return 0;}
	
	umask(0);
	
	sid=setsid();
	if (sid<0) {return -1;}
	
	if((chdir("/"))<0){return -1;}
	
	close(STDIN_FILENO);
	close(STDOUT_FILENO);
	close(STDERR_FILENO);
	
	fp = fopen ("SLABLog.txt", "a");
	fprintf(fp,"TIMESTAMP;ACTIVEOBJS;OBJSIZE;SLAB NAME;ACT;CT;VT;FVT;SVT;ZT;TrendTOTAL;ACM;CM;VM;FVM;SVM;ZM;TRENDMIDTERM;ACS;CS;VS;FVS;SVS;ZS;TRENDSHORTTERM\n");
	fclose(fp);
	slab_mk_values=NULL;

	while (1){
		slab_list=NULL;
		fp = fopen ("SLABLog.txt", "a");
		if (monitor(i*delay,slab_list,fp)){
			break;
		}
		fprintf(fp,"----ENDED----\n");
		fclose(fp);
		i+=1;		
		sleep(delay);
		
	} 
	
	free_slabinfo(slab_list);
	closelog();
	
	return 0;
}
