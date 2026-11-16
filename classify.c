/* classify.c
   All cell-separable invariant sequences of CRAFT with period dividing 4.
   I_t(x) = sum_{j high} <al[t][j], x_j> + sum_{j high} <al[t-1][j], S(x_{PN(j)})>
   Round t (tweakey TK_{t mod 4}) maps I_t to I_{t+1} iff for every high cell j, with i = PN(j),
     <al[t-1][j],S(w)> + <m_i(al[t]),w> + <al[t+1][j],S(w+k)> is constant in w,  k = TK_t[i],
   where m_{8+c} = al[t][c], m_{12+c} = al[t][c] + al[t][4+c].
   For each solution the weak tweak-key set is an affine space; its dimension and the dimension
   of its projection on the key are computed by elimination.
   Build: cc -O2 -o classify classify.c
*/
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
static const int S[16]={0xc,0xa,0xd,0x3,0xe,0xb,0xf,0x7,0x8,0x9,0x1,0x5,0x0,0x2,0x4,0x6};
static const int P[16]={15,12,13,14,10,9,8,11,6,5,4,7,1,2,3,0};
static const int Q[16]={12,10,15,5,14,8,9,2,11,3,7,4,6,0,1,13};
static int par(int v){ return __builtin_popcount(v)&1; }
static uint16_t Kset[16][16][16];      /* Kset[a][m][c] = set of k (bitmask) making the triple free */
static int al[4][8];
static int order[32][2], npos;
static int consAt[32][40][2], nconsAt[32];
typedef struct { uint64_t w[3]; int rhs; } Row;

static int mval(int t,int j){ /* mask m at low cell PN(j), from al[t] */
  int i=P[j], c=i&3; return i<12 ? al[t][c] : (al[t][c]^al[t][4+c]); }
static int cons_ok(int t,int j){ return Kset[al[(t+3)&3][j]][mval(t,j)][al[(t+1)&3][j]]!=0; }

/* elimination; returns rank, sets *incons if inconsistent */
static int elim(Row *r,int n,int *incons){ int rk=0; *incons=0;
  for(int b=0;b<192&&rk<n;b++){ int p=-1;
    for(int i=rk;i<n;i++) if((r[i].w[b>>6]>>(b&63))&1){p=i;break;}
    if(p<0) continue; Row t=r[p]; r[p]=r[rk]; r[rk]=t;
    for(int i=0;i<n;i++) if(i!=rk&&((r[i].w[b>>6]>>(b&63))&1)){ r[i].w[0]^=r[rk].w[0]; r[i].w[1]^=r[rk].w[1]; r[i].w[2]^=r[rk].w[2]; r[i].rhs^=r[rk].rhs; }
    rk++; }
  for(int i=rk;i<n;i++) if(r[i].rhs) *incons=1;
  return rk; }

static unsigned long long nsol=0, hist[130], histper[3][130], ncons=0;
static int best=-1; static int verbose=0; static int PER=4;


static int THR=0, PTHR=0; static int pairOK[16][16]; static int cellcost=0;
static int spdim(uint16_t a,uint16_t b){ uint16_t sp=0; for(int x=0;x<16;x++) if((a>>x)&1) for(int y=0;y<16;y++) if((b>>y)&1) sp|=1<<(x^y); return __builtin_popcount(sp)==16?4:__builtin_popcount(sp)==8?3:__builtin_popcount(sp)==4?2:__builtin_popcount(sp)==2?1:0; }
static int ccost(int j){ uint16_t V[4]; for(int t=0;t<4;t++){ int c=al[(t+1)&3][j]; V[t]=Kset[c][0][c]; }
  int a=4-spdim(V[0],V[1]), b=4-spdim(V[2],V[3]); return a>b?a:b; }
static int doneC[40][2], ndone=0;
/* weak-class dimensions from the constraints in doneC; returns key dimension or -1 if inconsistent */
static int dims(int *pdout){
  Row rows[160], r2[160]; int n=0;
  for(int q=0;q<ndone;q++){ int t=doneC[q][0], j=doneC[q][1]; int i=P[j]; int c=al[(t+1)&3][j];
    uint16_t ks=Kset[al[(t+3)&3][j]][mval(t,j)][c]; if(ks==0xffff) continue; int k0=__builtin_ctz(ks);
    uint16_t span=1;
    for(int lam=1;lam<16;lam++){ int ok=1; if((span>>lam)&1) continue;
      for(int k=0;k<16;k++) if((ks>>k)&1) if(par(lam&(k^k0))) ok=0;
      if(!ok) continue;
      { uint16_t s2=span; for(int x=0;x<16;x++) if((span>>x)&1) s2|=1<<(x^lam); span=s2; }
      Row r; memset(&r,0,sizeof r); r.rhs=par(lam&k0);
      int kcell=(t&1?64:0)+4*i, tcell=128+4*((t&2)?Q[i]:i);
      for(int b=0;b<4;b++) if((lam>>b)&1){ r.w[(kcell+b)>>6]^=1ULL<<((kcell+b)&63); r.w[(tcell+b)>>6]^=1ULL<<((tcell+b)&63); }
      rows[n++]=r; } }
  int inc; memcpy(r2,rows,sizeof(Row)*n); int rk=elim(r2,n,&inc); if(inc) return -1;
  for(int i=0;i<n;i++){ r2[i]=rows[i]; r2[i].w[0]=0; r2[i].w[1]=0; r2[i].rhs=0; }
  int inc2; int rT=elim(r2,n,&inc2); if(pdout) *pdout=192-rk; return 128-rk+rT; }
static FILE *dump=NULL;
static void evaluate(void){
  int nz=0; for(int t=0;t<4;t++) for(int j=0;j<8;j++) nz|=al[t][j]; if(!nz) return;
  nsol++; int pd; int kd=dims(&pd); if(kd<0) return; ncons++;
  int per=4; { int p2=1,p1=1; for(int j=0;j<8;j++){ if(al[0][j]!=al[2][j]||al[1][j]!=al[3][j]) p2=0; if(al[0][j]!=al[1][j]) p1=0; }
    if(p2) per=p1?1:2; }
  hist[kd]++; histper[per==1?0:per==2?1:2][kd]++;
  if(dump){ fprintf(dump,"%d %d %d ",kd,pd,per); for(int t=0;t<4;t++){ for(int j=0;j<8;j++) fprintf(dump,"%x",al[t][j]); fputc(t<3?' ':'\n',dump); } }
  if(kd>best) best=kd;
}
static void dfs(int pos){
  if(pos==npos){ evaluate(); return; }
  int t=order[pos][0], j=order[pos][1];
  for(int v=0;v<16;v++){ for(int tt=t;tt<4;tt+=PER) al[tt][j]=v; int ok=1;
    for(int q=0;q<nconsAt[pos]&&ok;q++) ok=cons_ok(consAt[pos][q][0],consAt[pos][q][1]);
    if(!ok) continue;
    if(PER==4&&t>=2&&!pairOK[al[t-2][j]][v]) continue;
    int cc=0; if(PER==4&&THR&&t==3){ cc=ccost(j); if(cellcost+cc>128-THR) continue; }
    int nd0=ndone; for(int q=0;q<nconsAt[pos];q++){ doneC[ndone][0]=consAt[pos][q][0]; doneC[ndone++][1]=consAt[pos][q][1]; }
    if((THR||PTHR)&&nconsAt[pos]&&pos<npos-1&&(PER!=4||t==3)){ int pdd; int kd=dims(&pdd); if(kd<THR||pdd<PTHR){ ndone=nd0; continue; } }
    cellcost+=cc; dfs(pos+1); cellcost-=cc; ndone=nd0; }
  for(int tt=t;tt<4;tt+=PER) al[tt][j]=0;
}
int main(int argc,char **argv){
  if(argc>1) PER=atoi(argv[1]); if(argc>2) THR=atoi(argv[2]); if(argc>3) dump=fopen(argv[3],"w"); if(argc>4) PTHR=atoi(argv[4]);
  for(int a=0;a<16;a++) for(int m=0;m<16;m++) for(int c=0;c<16;c++){ uint16_t ks=0;
    for(int k=0;k<16;k++){ int v0=0,ok=1; for(int w=0;w<16;w++){ int v=par(a&S[w])^par(m&w)^par(c&S[w^k]); if(!w) v0=v; else if(v!=v0) ok=0; }
      if(ok) ks|=1<<k; }
    Kset[a][m][c]=ks; }
  for(int a=0;a<16;a++) for(int c=0;c<16;c++){ int f=0,g=0; for(int m=0;m<16;m++){ f|=Kset[a][m][c]!=0; g|=Kset[c][m][a]!=0; } pairOK[a][c]=f&&g; }
  /* self-test of the table: every nonempty Kset is a coset of a subspace; known entries */
  for(int a=0;a<16;a++) for(int m=0;m<16;m++) for(int c=0;c<16;c++){ uint16_t ks=Kset[a][m][c]; if(!ks) continue;
    int k0=__builtin_ctz(ks); for(int x=0;x<16;x++) for(int y=0;y<16;y++) if(((ks>>x)&1)&&((ks>>y)&1)&&!((ks>>(x^y^k0))&1)){ puts("Kset not a coset"); return 1; } }
  if(Kset[5][5][5]!=((1<<5)|(1<<7)|(1<<13)|(1<<15))||Kset[5][0][5]!=((1<<0)|(1<<2)|(1<<8)|(1<<10))||Kset[0][0][0]!=0xffff){ puts("Kset self-test WRONG"); return 1; }
  int o=0;
  if(PER==4){ static const int co[8]={0,6,3,7,2,4,1,5}; static const int to[4]={0,2,1,3};
  for(int q=0;q<8;q++) for(int u=0;u<4;u++){ order[o][0]=to[u]; order[o++][1]=co[q]; }
  } else if(PER==2){
  for(int j=0;j<4;j++){ order[o][0]=1; order[o++][1]=j; }
  for(int j=4;j<8;j++){ order[o][0]=0; order[o++][1]=j; }
  for(int j=0;j<4;j++){ order[o][0]=0; order[o++][1]=j; }
  for(int j=4;j<8;j++){ order[o][0]=1; order[o++][1]=j; }
  } else { for(int j=0;j<8;j++){ order[o][0]=0; order[o++][1]=j; } }
  npos=o;
  int posOf[4][8]; for(int p=0;p<npos;p++) for(int tt=order[p][0];tt<4;tt+=PER) posOf[tt][order[p][1]]=p;
  int tot=0;
  for(int t=0;t<4;t++) for(int j=0;j<8;j++){ int i=P[j],c=i&3; int last=posOf[(t+3)&3][j];
    if(posOf[(t+1)&3][j]>last) last=posOf[(t+1)&3][j];
    if(posOf[t][c]>last) last=posOf[t][c];
    if(i>=12&&posOf[t][4+c]>last) last=posOf[t][4+c];
    consAt[last][nconsAt[last]][0]=t; consAt[last][nconsAt[last]++][1]=j; tot++; }
  if(tot!=32){ puts("constraint bookkeeping WRONG"); return 1; }
  /* self-test: the all-5 stationary sequence must give 2^108 weak keys and 2^144 weak pairs */
  for(int t=0;t<4;t++) for(int j=0;j<8;j++) al[t][j]=5;
  for(int t=0;t<4;t++) for(int j=0;j<8;j++) if(!cons_ok(t,j)){ puts("all-5 not a solution: WRONG"); return 1; }
  ndone=0; for(int t=0;t<4;t++) for(int j=0;j<8;j++){ doneC[ndone][0]=t; doneC[ndone++][1]=j; }
  evaluate(); ndone=0; if(best!=108||hist[108]!=1){ printf("self-test all-5: kd=%d WRONG\n",best); return 1; }
  puts("self-test: all-5 sequence gives 2^108 weak keys: ok");
  nsol=0; ncons=0; best=-1; memset(hist,0,sizeof hist); memset(histper,0,sizeof histper); memset(al,0,sizeof al);
  dfs(0);
  printf("nonzero sequences of period dividing 4: %llu, with nonempty weak class: %llu\n",nsol,ncons);
  printf("log2(weak keys) : count  (period 1 / period 2 / period 4)\n");
  for(int d=128;d>=0;d--) if(hist[d]) printf("  %3d : %llu  (%llu / %llu / %llu)\n",d,hist[d],histper[0][d],histper[1][d],histper[2][d]);
  return 0;
}
