// Line search for chains (Halfar's Theorem D rule), in C.
// A chain = pieces (rows) joined by weight-3 seams, blocks in distinct rotation classes, first entry 12..k.
// keep(r,d): 0 < a r - b d (<= c if c given);  bad: a r - b d > c.
// Usage: linesearch a b c [nodelimit] [parts part]     (c = 0: no cutoff, report the maximum surplus)
// Build: gcc -O2 -DN=9 -o line9 linesearch.c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifndef N
#define N 9
#endif
#define M1 (N-1)
static int NP, NC;
static unsigned char (*perm)[N];
static int *pidx, *cls, *tau2, *exitp, (*succ3)[5];
static unsigned char *used;
static long long A,B,C, nodes, nodelimit, bad, maxsur=-1; static long long hist[4096];
static int maxdepth, PARTS=1, PART=0, GDEPTH=0;
static int pack(const unsigned char *p){ int v=0; for(int i=0;i<N;i++) v=v*N+p[i]; return v; }
static void gen(unsigned char *p,int k,int um){ if(k==N){ memcpy(perm[NP],p,N); pidx[pack(p)]=NP; NP++; return; } for(int a=0;a<N;a++) if(!(um>>a&1)){ p[k]=a; gen(p,k+1,um|1<<a); } }
static void setup(void){
    long sz=1; for(int i=0;i<N;i++) sz*=N; long f=1; for(int i=2;i<=N;i++) f*=i;
    pidx=malloc(sizeof(int)*sz); perm=malloc(f*N); cls=malloc(sizeof(int)*f); tau2=malloc(sizeof(int)*f); exitp=malloc(sizeof(int)*f); succ3=malloc(sizeof(int)*5*f);
    unsigned char p[N]; NP=0; gen(p,0,0);
    int *cid=malloc(sizeof(int)*NP); for(int i=0;i<NP;i++) cid[i]=-1; NC=0;
    for(int i=0;i<NP;i++){ unsigned char q[N]; int z=0; while(perm[i][z]!=0) z++; for(int k=0;k<N;k++) q[k]=perm[i][(z+k)%N]; int c=pidx[pack(q)]; if(cid[c]<0) cid[c]=NC++; cls[i]=cid[c]; }
    static const int ord[5][3]={{1,0,2},{1,2,0},{0,2,1},{2,0,1},{2,1,0}};
    for(int i=0;i<NP;i++){ unsigned char q[N];
        for(int k=0;k<N-2;k++) q[k]=perm[i][k+1]; q[N-2]=perm[i][0]; q[N-1]=perm[i][N-1]; tau2[i]=pidx[pack(q)];
        q[0]=perm[i][N-1]; for(int k=1;k<N;k++) q[k]=perm[i][k-1]; exitp[i]=pidx[pack(q)];
        for(int s=0;s<5;s++){ for(int k=3;k<N;k++) q[k-3]=perm[i][k]; for(int k=0;k<3;k++) q[N-3+k]=perm[i][ord[s][k]]; succ3[i][s]=pidx[pack(q)]; } }
    used=calloc(NC,1); free(cid);
}
static int stop;
static void dfs(int q,int r,long long d){   // chain with r pieces, deficit d, last exit q; already known kept
    nodes++; if(r>maxdepth) maxdepth=r;
    if(nodelimit && nodes>nodelimit){ stop=1; return; }
    if(PARTS>1 && r==GDEPTH && (q%PARTS)!=PART) return;
    for(int s=0;s<5 && !stop;s++){
        int e=succ3[q][s]; int len=0, ee=e; int added[M1];
        while(len<M1 && !used[cls[ee]]){
            used[cls[ee]]=1; added[len++]=cls[ee];
            long long sur=A*(r+1)-B*(d+(M1-len));
            if(sur>maxsur){ maxsur=sur; }
            if(C && sur>C){ bad++; }
            else if(sur>0){ dfs(exitp[ee],r+1,d+(M1-len)); if(stop) break; }
            ee=tau2[ee];
        }
        for(int k=0;k<len;k++) used[added[k]]=0;
    }
}
int main(int argc,char**argv){
    A=atoll(argv[1]); B=atoll(argv[2]); C=atoll(argv[3]); nodelimit=argc>4?atoll(argv[4]):0;
    if(argc>7){ PARTS=atoi(argv[5]); PART=atoi(argv[6]); GDEPTH=atoi(argv[7]); }
    setup(); clock_t t0=clock();
    unsigned char p0[N]; for(int i=0;i<N;i++) p0[i]=i; int e=pidx[pack(p0)], len=0, ee=e;
    while(len<M1){ used[cls[ee]]=1; len++; long long sur=A-B*(M1-len); if(sur>maxsur) maxsur=sur; if(C&&sur>C) bad++; else if(sur>0) dfs(exitp[ee],1,M1-len); ee=tau2[ee]; if(stop) break; }
    printf("k=%d line %lld r <= %lld d + %lld : kept %lld bad %lld maxsurplus %lld maxdepth %d %s %.1fs\n",N,A,B,C,nodes,bad,maxsur,maxdepth,stop?"(NODE LIMIT)":"",(double)(clock()-t0)/CLOCKS_PER_SEC);
    return 0;
}
