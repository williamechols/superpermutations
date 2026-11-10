// Halfar's window search (SSearch.lean, Theorem C) in C.
// Usage: window cn q [bn] [nodelimit]      with bn omitted or 0: report the least bn that passes.
// Build: gcc -O2 -DN=9 -o win9 window.c
#include "tables.h"
static long long A,Q2,C1,C2,BN, nodes, nodelimit, viol, maxneed=-(1LL<<60); static int maxdepth, stop;
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
    walk(0,0,0,1,0);
    printf("k=%d c=%lld/%lld bn=%lld : states %lld violations %lld least_bn %lld maxdepth %d %s %.1fs\n",N,cn,q,BN,nodes,viol,maxneed,maxdepth,stop?"(NODE LIMIT)":"",(double)(clock()-t0)/CLOCKS_PER_SEC);
    return 0;
}
