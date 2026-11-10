// Shared tables for chain searches on N symbols, permutations indexed by Lehmer rank.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifndef N
#define N 9
#endif
#define M1 (N-1)
static long NP, NC;
static int *cls, *tau2, *exitp, (*succ3)[5];
static unsigned char *used;
static long fact[16];
static long rankp(const unsigned char *p,int n){ long r=0; for(int i=0;i<n;i++){ int c=0; for(int j=i+1;j<n;j++) if(p[j]<p[i]) c++; r+=c*fact[n-1-i]; } return r; }
static void unrank(long r,unsigned char *p,int n){ unsigned char el[16]; for(int i=0;i<n;i++) el[i]=i; for(int i=0;i<n;i++){ int c=r/fact[n-1-i]; r%=fact[n-1-i]; p[i]=el[c]; for(int j=c;j<n-1-i;j++) el[j]=el[j+1]; } }
static long clsof(const unsigned char *p){ unsigned char q[16]; int z=0; while(p[z]!=0) z++; for(int k=1;k<N;k++) q[k-1]=p[(z+k)%N]-1; return rankp(q,N-1); }
static void setup(void){
    fact[0]=1; for(int i=1;i<16;i++) fact[i]=fact[i-1]*i;
    NP=fact[N]; NC=fact[N-1];
    cls=malloc(sizeof(int)*NP); tau2=malloc(sizeof(int)*NP); exitp=malloc(sizeof(int)*NP); succ3=malloc(sizeof(int)*5*NP);
    static const int ord[5][3]={{1,0,2},{1,2,0},{0,2,1},{2,0,1},{2,1,0}};
    for(long i=0;i<NP;i++){ unsigned char p[16], q[16]; unrank(i,p,N);
        cls[i]=clsof(p);
        for(int k=0;k<N-2;k++) q[k]=p[k+1]; q[N-2]=p[0]; q[N-1]=p[N-1]; tau2[i]=rankp(q,N);
        q[0]=p[N-1]; for(int k=1;k<N;k++) q[k]=p[k-1]; exitp[i]=rankp(q,N);
        for(int s=0;s<5;s++){ for(int k=3;k<N;k++) q[k-3]=p[k]; for(int k=0;k<3;k++) q[N-3+k]=p[ord[s][k]]; succ3[i][s]=rankp(q,N); } }
    used=calloc(NC,1);
}
