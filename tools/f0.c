// Chain-cap search F0 on 7 symbols, a re-implementation of Halfar's PS.seqSearch with s = 0
// (proofs/lean/n7/LowerBounds/PSearch.lean), used to count nodes for candidate cap tables.
// Usage: f0 lo hi T0 T1 ... T_hi   -> prints found/not found and the node count.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define K 7
#define NP 5040
static int perm[NP][K];
static int code2idx[1 << 21];  // 3 bits per digit (digits 1..7)
static int cls[NP], nxtE[NP], s3[NP][6], ns3[NP];
static int T[200], lo, hi;
static unsigned char keepTab[400][200];
static uint64_t used[12];
static long long nodes;
static long long limit = -1;

static int enc(const int *p) { int c = 0; for (int i = 0; i < K; i++) c = c * 8 + p[i]; return c; }

static void gen(void) {
  int n = 0, p[K];
  // lexicographic permutations of 1..7
  for (int i = 0; i < K; i++) p[i] = i + 1;
  while (1) {
    memcpy(perm[n], p, sizeof p); code2idx[enc(p)] = n; n++;
    int i = K - 2; while (i >= 0 && p[i] > p[i + 1]) i--;
    if (i < 0) break;
    int j = K - 1; while (p[j] < p[i]) j--;
    int t = p[i]; p[i] = p[j]; p[j] = t;
    for (int a = i + 1, b = K - 1; a < b; a++, b--) { t = p[a]; p[a] = p[b]; p[b] = t; }
  }
  // classes: canonical rotation starting with 7
  int ncls = 0; static int canon2cls[NP]; for (int i = 0; i < NP; i++) canon2cls[i] = -1;
  for (int i = 0; i < NP; i++) {
    int q[K], s = 0; while (perm[i][s] != K) s++;
    for (int a = 0; a < K; a++) q[a] = perm[i][(s + a) % K];
    int ci = code2idx[enc(q)];
    if (canon2cls[ci] < 0) canon2cls[ci] = ncls++;
    cls[i] = canon2cls[ci];
  }
  if (ncls != 720) { fprintf(stderr, "ncls %d\n", ncls); exit(1); }
  for (int i = 0; i < NP; i++) {
    int x[K], y[K];
    // exit: last digit to the front
    x[0] = perm[i][K - 1]; for (int a = 1; a < K; a++) x[a] = perm[i][a - 1];
    // door: x3..x7 x2 x1
    for (int a = 0; a < K - 2; a++) y[a] = x[a + 2];
    y[K - 2] = x[1]; y[K - 1] = x[0];
    nxtE[i] = code2idx[enc(y)];
    // weight-3 successors: words whose first 4 letters are the last 4 of the exit
    ns3[i] = 0;
    for (int j = 0; j < NP; j++) {
      int ok = 1; for (int a = 0; a < K - 3; a++) if (perm[j][a] != x[a + 3]) { ok = 0; break; }
      if (ok) s3[i][ns3[i]++] = j;
    }
  }
}

static int isUsed(int c) { return (used[c >> 6] >> (c & 63)) & 1; }
static void setU(int c) { used[c >> 6] |= 1ULL << (c & 63); }
static void clrU(int c) { used[c >> 6] &= ~(1ULL << (c & 63)); }

static int go(int r, int d, int q);

// rows starting with the block entered at D; returns 1 if found
static int walk(int D, int r, int d) {
  int marked[6], nm = 0, cur = D, res = 0;
  for (int n = K - 1; n >= 1; n--) {
    if (isUsed(cls[cur])) break;
    setU(cls[cur]); marked[nm++] = cls[cur];
    if (go(r + 1, d + (n - 1), cur)) { res = 1; break; }
    cur = nxtE[cur];
  }
  for (int a = 0; a < nm; a++) clrU(marked[a]);
  return res;
}

static int go(int r, int d, int q) {
  nodes++;
  if (limit >= 0 && nodes > limit) { printf("LIMIT\n"); exit(2); }
  if (lo <= d && d <= hi && T[d] < r) return 1;
  if (d > hi || r >= 400) return 0;
  if (!keepTab[r][d]) return 0;
  for (int a = 0; a < ns3[q]; a++) if (walk(s3[q][a], r, d)) return 1;
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage\n"); return 1; }
  lo = atoi(argv[1]); hi = atoi(argv[2]);
  if (argc != 3 + hi + 1 && argc != 3 + hi + 2) { fprintf(stderr, "need %d caps\n", hi + 1); return 1; }
  for (int x = 0; x <= hi; x++) T[x] = atoi(argv[3 + x]);
  if (argc == 3 + hi + 2) limit = atoll(argv[3 + hi + 1]);
  gen();
  for (int r = 0; r < 400; r++)
    for (int d = 0; d <= hi; d++) {
      int k = 0;
      for (int x = 0; x <= hi; x++)
        if (lo <= x && d <= x && T[x] < r + T[x - d]) { k = 1; break; }
      keepTab[r][d] = k;
    }
  int st = code2idx[enc((int[]){1, 2, 3, 4, 5, 6, 7})];
  int found = walk(st, 0, 0) ;
  // walk starts the first row: go(1, holes, e) -- matches searchPart (t=0, r=1)
  printf("%s nodes %lld\n", found ? "FOUND" : "none", nodes);
  return 0;
}
