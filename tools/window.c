// Halfar's window search (SSearch.lean, Theorem C) in C.
// Usage: window cn q [bn] [nodelimit]      with bn omitted or 0: report the least bn that passes.
// Build: gcc -O2 -DN=9 -o win9 window.c
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
static long long A,Q2,C1,C2,BN, nodes, nodelimit, viol, maxneed=-(1LL<<60); static int maxdepth, stop;
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
static void go(int y,long long P,long long Nn,int f,int depth);
// a piece of deficit d ending with exit x, after state (P,Nn,f)
static inline void kid(long long P,long long Nn,int f,int d,int x,int depth){
    if(d==0){ if(f==1) return; go(x,P,Nn+Q2,0,depth+1); return; }
    if(Nn+Q2+C2<=P+A*d) return;
    if(f==0){ if(Nn<=P) return; go(x,P+A*d,Nn+Q2,d>=2?2:1,depth+1); return; }
    go(x,P+A*d,Nn+Q2,d>=2?2:f,depth+1);
}
static void walk(int e,long long P,long long Nn,int f,int depth){
    int len=0, ee=e, added[M1];
    while(len<M1 && !used[cls[ee]] && !stop){ used[cls[ee]]=1; added[len++]=cls[ee]; kid(P,Nn,f,M1-len,exitp[ee],depth); ee=tau2[ee]; }
    for(int k=0;k<len;k++) used[added[k]]=0;
}
static void go(int y,long long P,long long Nn,int f,int depth){
    nodes++; if(depth>maxdepth) maxdepth=depth;
    if(nodelimit && nodes>nodelimit){ stop=1; return; }
    if(f==2){ long long need=Nn+C1-P; if(need>maxneed) maxneed=need; if(BN>=0 && need>BN){ viol++; return; } }
    for(int s=0;s<5 && !stop;s++) walk(succ3[y][s],P,Nn,f,depth);
}
int main(int argc,char**argv){
    long long cn=atoll(argv[1]), q=atoll(argv[2]); BN=argc>3?atoll(argv[3]):-1; nodelimit=argc>4?atoll(argv[4]):0;
    A=q*(N-3)-cn; Q2=2*q; C1=2*q*(N-4); C2=2*q*(N-3);
    setup(); clock_t t0=clock();
    unsigned char p0[N]; for(int i=0;i<N;i++) p0[i]=i;
    walk(pidx[pack(p0)],0,0,1,0);
    printf("k=%d c=%lld/%lld bn=%lld : states %lld violations %lld least_bn %lld maxdepth %d %s %.1fs\n",N,cn,q,BN,nodes,viol,maxneed,maxdepth,stop?"(NODE LIMIT)":"",(double)(clock()-t0)/CLOCKS_PER_SEC);
    return 0;
}
