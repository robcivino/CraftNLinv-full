// ============================================================================
// craft_invattack.cpp
//
// Weak-key invariants of full (32-round) CRAFT and the chosen-tweak key
// recovery built on them.  C++17, no external dependencies.
//
// Build:   c++ -std=c++17 -O2 -o craft_invattack craft_invattack.cpp
// Run:     ./craft_invattack selftest
//          ./craft_invattack conditions 05b005b0 00004200 05b005b0 00004200
//          ./craft_invattack phase1   [--keys N] [--seed s]
//          ./craft_invattack v2       [--keys N] [--seed s]
//          ./craft_invattack attack   [--lib file]... [--keys N] [--budget d] [--qbudget log2] [--seed s]
//
// Conventions (same as the paper): state = 16 nibbles, cell 4*row+col, nibble 0
// is the first hex digit; cells 0..7 are "high" (rows 0,1), 8..15 "low".
// A mask sequence al[t][j], t = 0..3 (round residue mod 4), j = 0..7 (high
// cell), defines the state function
//     I_t(x) = sum_j <al[t][j], x_j>  +  sum_j <al[t-1][j], S(x_{P[j]})> ,
// x being the state entering MixColumn of round t.  Round t carries I_t to
// I_{t+1} up to a constant iff for every high cell j, with i = P[j], the
// triple (al[t-1][j], m_i(al[t]), al[t+1][j]) is free for k = TK_t[i], i.e.
//     <a,S(w)> + <m,w> + <c,S(w+k)>  is constant in w,
// where m_{8+c} = al[t][c] and m_{12+c} = al[t][c] + al[t][4+c].
// ============================================================================
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
#include <string>
#include <array>
#include <algorithm>
#include <random>
#include <chrono>
#include <fstream>
#include <sstream>
#include <iostream>
#include <cmath>
#include <utility>

// ----------------------------------------------------------------------------
// 1. The cipher
// ----------------------------------------------------------------------------
namespace craft {
static const uint8_t S[16]={0xc,0xa,0xd,0x3,0xe,0xb,0xf,0x7,0x8,0x9,0x1,0x5,0x0,0x2,0x4,0x6};
static const uint8_t P[16]={15,12,13,14,10,9,8,11,6,5,4,7,1,2,3,0};
static const uint8_t Q[16]={12,10,15,5,14,8,9,2,11,3,7,4,6,0,1,13};
static uint8_t RCa[32], RCb[32];

// Round constants from the two LFSRs (4-bit and 3-bit), as in the reference
// implementation that reproduces the designers' test vectors.
static void init_constants(){
    int a=1,b=1;
    for(int r=0;r<32;r++){
        RCa[r]=(uint8_t)a; RCb[r]=(uint8_t)b;
        int a3=(a>>3)&1,a2=(a>>2)&1,a1=(a>>1)&1,a0=a&1;
        a=((a1^a0)<<3)|(a3<<2)|(a2<<1)|a1;
        int b2=(b>>2)&1,b1=(b>>1)&1,b0=b&1;
        b=((b1^b0)<<2)|(b2<<1)|b1;
    }
}
typedef std::array<uint8_t,16> Nib;
static inline void mc(Nib& x){ for(int c=0;c<4;c++){ x[c]^=x[8+c]^x[12+c]; x[4+c]^=x[12+c]; } }
struct Tweakeys { Nib tk[4]; };
static Tweakeys schedule(const Nib& k0,const Nib& k1,const Nib& t){
    Tweakeys s;
    for(int i=0;i<16;i++){ s.tk[0][i]=k0[i]^t[i]; s.tk[1][i]=k1[i]^t[i];
                            s.tk[2][i]=k0[i]^t[Q[i]]; s.tk[3][i]=k1[i]^t[Q[i]]; }
    return s;
}
// R-round encryption, rounds 0..R-1, the last one without PN and SB.
static Nib encrypt(const Nib& p,const Tweakeys& s,int R){
    Nib x=p,y;
    for(int r=0;r<R;r++){
        mc(x); x[4]^=RCa[r]; x[5]^=RCb[r];
        for(int i=0;i<16;i++) x[i]^=s.tk[r&3][i];
        if(r<R-1){ for(int i=0;i<16;i++) y[P[i]]=x[i]; for(int i=0;i<16;i++) x[i]=S[y[i]]; }
    }
    return x;
}
static Nib decrypt(const Nib& c,const Tweakeys& s,int R){
    Nib x=c,y;
    for(int r=R-1;r>=0;r--){
        if(r<R-1){ for(int i=0;i<16;i++) y[i]=S[x[i]]; for(int i=0;i<16;i++) x[i]=y[P[i]]; }
        for(int i=0;i<16;i++) x[i]^=s.tk[r&3][i];
        x[4]^=RCa[r]; x[5]^=RCb[r]; mc(x);
    }
    return x;
}
static Nib fromhex(const char* s){ Nib x; for(int i=0;i<16;i++){ char ch=s[i]; x[i]=(uint8_t)(ch<='9'?ch-'0':(ch|32)-'a'+10); } return x; }
static std::string tohex(const Nib& x){ std::string s; for(int i=0;i<16;i++) s+="0123456789abcdef"[x[i]]; return s; }
static bool selftest(){
    Nib k0=fromhex("27A6781A43F364BC"),k1=fromhex("916708D5FBB5AEFE"),t=fromhex("54CD94FFD0670A58");
    Nib p=fromhex("5734F006D8D88A3E"),e=fromhex("A17D6BD4BEEB996F");
    Tweakeys s=schedule(k0,k1,t);
    Nib c=encrypt(p,s,32);
    if(c!=e){ printf("CIPHER SELF-TEST FAILED: got %s expected %s\n",tohex(c).c_str(),tohex(e).c_str()); return false; }
    if(decrypt(c,s,32)!=p){ puts("CIPHER SELF-TEST FAILED: decryption"); return false; }
    for(int x=0;x<16;x++) if(S[S[x]]!=x||P[P[x]]!=x){ puts("S or P not an involution"); return false; }
    return true;
}
} // namespace craft

// ----------------------------------------------------------------------------
// 2. Free triples of the S-box.  Kset[a][m][c] = bitmask of the k such that
//    <a,S(w)> + <m,w> + <c,S(w+k)> is constant in w.
// ----------------------------------------------------------------------------
static inline int par(unsigned v){ return __builtin_parity(v); }
static uint16_t Kset[16][16][16];
static void build_kset(){
    using craft::S;
    for(int a=0;a<16;a++) for(int m=0;m<16;m++) for(int c=0;c<16;c++){
        uint16_t ks=0;
        for(int k=0;k<16;k++){ int v0=0,ok=1;
            for(int w=0;w<16;w++){ int v=par(a&S[w])^par(m&w)^par(c&S[w^k]); if(!w) v0=v; else if(v!=v0){ok=0;break;} }
            if(ok) ks|=(uint16_t)(1u<<k); }
        Kset[a][m][c]=ks;
    }
}
static bool kset_selftest(){
    // Values proved by hand in the report (Lemma on free triples).
    struct { int a,m,c; uint16_t ks; } tab[]={
        {5,5,5,(uint16_t)((1<<5)|(1<<7)|(1<<13)|(1<<15))},   // {5,7,d,f}
        {5,0,5,(uint16_t)((1<<0)|(1<<2)|(1<<8)|(1<<10))},    // {0,2,8,a}
        {5,4,5,(uint16_t)((1<<1)|(1<<3)|(1<<9)|(1<<11))},    // {1,3,9,b}
        {5,1,5,(uint16_t)((1<<4)|(1<<6)|(1<<12)|(1<<14))},   // {4,6,c,e}
        {2,5,2,(uint16_t)((1<<5)|(1<<7)|(1<<8)|(1<<10))},    // {5,7,8,a}
        {4,0xb,4,(uint16_t)(1<<13)},                          // {d}
        {1,0xe,1,(uint16_t)(1<<13)},                          // {d}
        {0xb,2,0xb,(uint16_t)(1<<8)},                         // {8}
        {0xb,0,0xb,(uint16_t)(1<<0)},                         // {0}
        {0xe,2,0xe,(uint16_t)(1<<8)},                         // {8}
        {8,0xa,8,(uint16_t)(1<<5)},                           // {5}
        {0,0,0,(uint16_t)0xffff} };
    for(auto& e:tab) if(Kset[e.a][e.m][e.c]!=e.ks){ printf("Kset self-test failed at (%x,%x,%x): %04x vs %04x\n",e.a,e.m,e.c,Kset[e.a][e.m][e.c],e.ks); return false; }
    // every nonempty Kset is a coset of a subspace
    for(int a=0;a<16;a++) for(int m=0;m<16;m++) for(int c=0;c<16;c++){ uint16_t ks=Kset[a][m][c]; if(!ks) continue;
        int k0=__builtin_ctz(ks); for(int x=0;x<16;x++) for(int y=0;y<16;y++) if(((ks>>x)&1)&&((ks>>y)&1)&&!((ks>>(x^y^k0))&1)){ puts("Kset not a coset"); return false; } }
    return true;
}

// ----------------------------------------------------------------------------
// 3. F2 linear algebra.  Variables: K0 bit 4i+b -> column 4i+b (0..63),
//    K1 -> 64..127, T nibble j bit b -> 128+4j+b (128..191).
// ----------------------------------------------------------------------------
struct Row { uint64_t w[3]; int rhs; };
static inline int  bit(const uint64_t* w,int c){ return (int)((w[c>>6]>>(c&63))&1); }
static inline void flip(uint64_t* w,int c){ w[c>>6]^=1ull<<(c&63); }

struct KVec { uint64_t w[2]; };                 // a linear form on the 128 key bits
static inline bool kzero(const KVec& v){ return !(v.w[0]|v.w[1]); }
static inline int  klow(const KVec& v){ return v.w[0]? __builtin_ctzll(v.w[0]) : 64+__builtin_ctzll(v.w[1]); }
static inline int  kbit(const KVec& v,int c){ return (int)((v.w[c>>6]>>(c&63))&1); }
static inline void kxor(KVec& a,const KVec& b){ a.w[0]^=b.w[0]; a.w[1]^=b.w[1]; }
static inline int  keval(const KVec& v,const uint64_t* key){ return __builtin_parityll(v.w[0]&key[0])^__builtin_parityll(v.w[1]&key[1]); }

// Knowledge about the key: a consistent system of affine equations in RREF.
struct Knowledge {
    struct E { KVec v; int pivot; int rhs; };
    std::vector<E> rows;
    int rank() const { return (int)rows.size(); }
    // reduce v by the system; returns residual, accumulates the rhs into *val
    KVec reduce(KVec v,int* val) const { for(const E& e:rows) if(kbit(v,e.pivot)){ kxor(v,e.v); *val^=e.rhs; } return v; }
    // returns 1 if new information was added, 0 if implied, -1 if contradiction
    int add(KVec v,int rhs){
        int val=0; KVec r=reduce(v,&val);
        if(kzero(r)) return (val==rhs)?0:-1;
        int piv=klow(r);
        for(E& e:rows) if(kbit(e.v,piv)){ kxor(e.v,r); e.rhs^=(rhs^val); }
        rows.push_back({r,piv,rhs^val});
        return 1;
    }
    bool consistent_with(const uint64_t* key) const { for(const E& e:rows) if(keval(e.v,key)!=e.rhs) return false; return true; }
};

// ----------------------------------------------------------------------------
// 4. Mask sequences and their tweakey conditions
// ----------------------------------------------------------------------------
struct Seq {
    uint8_t al[4][8];
    int per=0;                 // 1, 2 or 4
    bool valid=false;
    // affine conditions in RREF, T columns eliminated first:
    struct TRow { KVec k; uint64_t tbits; int rhs; };   // one T bit (pivot) expressed through the key
    std::vector<TRow> trows;
    std::vector<std::pair<KVec,int>> krel;             // pure key relations (class membership)
    int rankT=0;               // number of T pivots
    int codim() const { return (int)krel.size(); }
    std::string name() const { std::string s; for(int t=0;t<4;t++){ for(int j=0;j<8;j++) s+="0123456789abcdef"[al[t][j]]; if(t<3) s+=' '; } return s; }
    int mval(int t,int j) const { int i=craft::P[j], c=i&3; return i<12? al[t][c] : (al[t][c]^al[t][4+c]); }
    uint16_t cond(int t,int j) const { return Kset[al[(t+3)&3][j]][mval(t,j)][al[(t+1)&3][j]]; }
};

static bool parse_seq(Seq& s,const std::string* a4){
    for(int t=0;t<4;t++){ if(a4[t].size()!=8) return false;
        for(int j=0;j<8;j++){ char ch=a4[t][j]; int v= ch<='9'? ch-'0' : (ch|32)-'a'+10; if(v<0||v>15) return false; s.al[t][j]=(uint8_t)v; } }
    bool p1=true,p2=true; for(int j=0;j<8;j++){ if(s.al[0][j]!=s.al[1][j]) p1=false; if(s.al[0][j]!=s.al[2][j]||s.al[1][j]!=s.al[3][j]) p2=false; }
    s.per= p1?1:(p2?2:4);
    return true;
}

// Build the affine system of the sequence and put it in RREF (T first, then K).
static void analyse_seq(Seq& s){
    s.valid=false; s.trows.clear(); s.krel.clear(); s.rankT=0;
    std::vector<Row> rows;
    for(int t=0;t<4;t++) for(int j=0;j<8;j++){
        uint16_t ks=s.cond(t,j); if(!ks) return;              // not an invariant sequence
        if(ks==0xffff) continue;
        int i=craft::P[j]; int k0=__builtin_ctz(ks); uint16_t span=1;
        for(int lam=1;lam<16;lam++){ if((span>>lam)&1) continue;   // lam in the annihilator of the coset's subspace, independent
            int ok=1; for(int k=0;k<16;k++) if(((ks>>k)&1)&&par(lam&(k^k0))) ok=0; if(!ok) continue;
            uint16_t s2=span; for(int x=0;x<16;x++) if((span>>x)&1) s2|=(uint16_t)(1u<<(x^lam)); span=s2;
            Row r; memset(&r,0,sizeof r); r.rhs=par(lam&k0);
            int kc=(t&1?64:0)+4*i, tc=128+4*((t&2)?craft::Q[i]:i);
            for(int b=0;b<4;b++) if((lam>>b)&1){ flip(r.w,kc+b); flip(r.w,tc+b); }
            rows.push_back(r);
        }
    }
    // RREF, columns in order 128..191 then 0..127
    int n=(int)rows.size(), rk=0;
    auto process=[&](int c){ if(rk>=n) return; int p=-1; for(int i=rk;i<n;i++) if(bit(rows[i].w,c)){p=i;break;} if(p<0) return;
        std::swap(rows[p],rows[rk]);
        for(int i=0;i<n;i++) if(i!=rk&&bit(rows[i].w,c)){ rows[i].w[0]^=rows[rk].w[0]; rows[i].w[1]^=rows[rk].w[1]; rows[i].w[2]^=rows[rk].w[2]; rows[i].rhs^=rows[rk].rhs; }
        rk++; };
    for(int c=128;c<192;c++) process(c);
    for(int c=0;c<128;c++) process(c);
    for(int i=rk;i<n;i++) if(rows[i].rhs) return;            // inconsistent (cannot happen for a valid sequence)
    for(int i=0;i<rk;i++){
        if(rows[i].w[2]){ Seq::TRow tr; tr.k.w[0]=rows[i].w[0]; tr.k.w[1]=rows[i].w[1]; tr.tbits=rows[i].w[2]; tr.rhs=rows[i].rhs; s.trows.push_back(tr); s.rankT++; }
        else { KVec v; v.w[0]=rows[i].w[0]; v.w[1]=rows[i].w[1]; s.krel.push_back({v,rows[i].rhs}); }
    }
    s.valid=true;
}
// log2 of the number of weak keys and of weak (key,tweak) pairs
static int seq_logkeys(const Seq& s){ return 128-s.codim(); }
static int seq_logpairs(const Seq& s){ return 192-s.rankT-s.codim(); }

// The two state functions used in the distinguisher: I_0 on the plaintext and
// G on the ciphertext of an R-round encryption (last round linear).
static int I0(const Seq& s,const craft::Nib& x){ int v=0; for(int j=0;j<8;j++){ v^=par(s.al[0][j]&x[j]); v^=par(s.al[3][j]&craft::S[x[craft::P[j]]]); } return v; }
static int Gc(const Seq& s,const craft::Nib& c,int R){ int t=(R-1)&3; craft::Nib m=c; craft::mc(m); int v=0;
    for(int j=0;j<8;j++){ v^=par(s.al[t][j]&m[j]); v^=par(s.al[(t+1)&3][j]&craft::S[c[craft::P[j]]]); v^=par(s.mval(t,j)&c[craft::P[j]]); } return v; }

// Given the true key, build a weak tweak for the sequence (free T bits random).
// Returns false if the key is not in the class of the sequence.
static bool weak_tweak(const Seq& s,const uint64_t key[2],std::mt19937_64& rng,craft::Nib& T){
    for(auto& kr:s.krel) if(keval(kr.first,key)!=kr.second) return false;
    uint64_t tb=rng();                                   // all 64 T bits random ...
    // ... then fix the pivot bits; non-pivot T bits keep their random value
    uint64_t pivmask=0; for(auto& tr:s.trows) pivmask|= (tr.tbits & -tr.tbits);   // lowest set bit = pivot (columns were processed in increasing order)
    tb&=~pivmask;
    for(auto& tr:s.trows){ uint64_t piv=tr.tbits & -tr.tbits; int v=tr.rhs^keval(tr.k,key)^__builtin_parityll(tr.tbits&~piv&tb); if(v) tb|=piv; }
    for(int j=0;j<16;j++) T[j]=(uint8_t)((tb>>(4*j))&15);
    return true;
}

// Key as two 64-bit words from nibble arrays (bit 4i+b of K0 -> word0, K1 -> word1)
static void pack_key(const craft::Nib& k0,const craft::Nib& k1,uint64_t key[2]){ key[0]=key[1]=0; for(int i=0;i<16;i++){ key[0]|=(uint64_t)k0[i]<<(4*i); key[1]|=(uint64_t)k1[i]<<(4*i);} }
static void unpack_key(const uint64_t key[2],craft::Nib& k0,craft::Nib& k1){ for(int i=0;i<16;i++){ k0[i]=(uint8_t)((key[0]>>(4*i))&15); k1[i]=(uint8_t)((key[1]>>(4*i))&15);} }
static craft::Nib random_nib(std::mt19937_64& rng){ uint64_t v=rng(); craft::Nib x; for(int i=0;i<16;i++) x[i]=(uint8_t)((v>>(4*i))&15); return x; }

// ----------------------------------------------------------------------------
// 5. Built-in sequences: the four 2^127 ones and the {0,5} skeleton family
// ----------------------------------------------------------------------------
static std::vector<Seq> builtin_sequences(bool skeleton){
    std::vector<Seq> L;
    const char* rows[4][4]={{"05b005b0","00004200","05b005b0","00004200"},{"05e005e0","00001200","05e005e0","00001200"},
                            {"00004200","05b005b0","00004200","05b005b0"},{"00001200","05e005e0","00001200","05e005e0"}};
    for(auto& r:rows){ std::string a[4]={r[0],r[1],r[2],r[3]}; Seq s; parse_seq(s,a); analyse_seq(s); if(s.valid) L.push_back(s); }
    if(skeleton){
        // mu on indicator vectors of high cells (bit j <-> cell j)
        auto mu=[](unsigned h){ unsigned m=0; auto g=[&](int j){ return (h>>j)&1u; };
            m|=g(0)<<6; m|=g(1)<<5; m|=g(2)<<4; m|=g(3)<<7; m|=(g(0)^g(4))<<1; m|=(g(1)^g(5))<<2; m|=(g(2)^g(6))<<3; m|=(g(3)^g(7))<<0; return m; };
        for(unsigned A=0;A<256;A++) for(unsigned B=0;B<256;B++){ if(!(A|B)) continue; if(mu(A)&~B) continue; if(mu(B)&~A) continue;
            Seq s; for(int j=0;j<8;j++){ s.al[0][j]=s.al[2][j]=(uint8_t)(((A>>j)&1)?5:0); s.al[1][j]=s.al[3][j]=(uint8_t)(((B>>j)&1)?5:0); }
            s.per=(A==B)?1:2; analyse_seq(s); if(s.valid) L.push_back(s); }
    }
    return L;
}
static int load_library(const char* fn,std::vector<Seq>& L){
    std::ifstream f(fn); if(!f){ printf("cannot open %s\n",fn); return 0; }
    std::string line; int n=0;
    while(std::getline(f,line)){ std::istringstream is(line); int kd,pd,per; std::string a[4]; if(!(is>>kd>>pd>>per>>a[0]>>a[1]>>a[2]>>a[3])) continue;
        Seq s; if(!parse_seq(s,a)) continue; analyse_seq(s); if(!s.valid) continue;
        if(seq_logkeys(s)!=kd||seq_logpairs(s)!=pd) printf("warning: %s: file says (%d,%d), recomputed (%d,%d)\n",s.name().c_str(),kd,pd,seq_logkeys(s),seq_logpairs(s));
        L.push_back(s); n++; }
    return n;
}
static void dedup_sort(std::vector<Seq>& L){
    std::sort(L.begin(),L.end(),[](const Seq& a,const Seq& b){ return memcmp(a.al,b.al,sizeof a.al)<0; });
    L.erase(std::unique(L.begin(),L.end(),[](const Seq& a,const Seq& b){ return memcmp(a.al,b.al,sizeof a.al)==0; }),L.end());
    // cheap and large-class sequences first
    std::stable_sort(L.begin(),L.end(),[](const Seq& a,const Seq& b){ if(a.codim()!=b.codim()) return a.codim()<b.codim(); return a.trows.size()<b.trows.size(); });
}

// ----------------------------------------------------------------------------
// 6. The oracle (encryption under the secret key, chosen tweak) and the attack
// ----------------------------------------------------------------------------
struct Oracle {
    craft::Nib k0,k1; uint64_t key[2]; long long queries=0;
    craft::Nib enc(const craft::Nib& p,const craft::Nib& t){ queries++; return craft::encrypt(p,craft::schedule(k0,k1,t),32); }
};

struct AttackStats { long long queries=0; int seq_tried=0, seq_success=0, seq_failed=0, seq_skipped=0; double log2patterns=0; };

// Chosen-tweak pattern search for one sequence given the current knowledge.
// Returns: 1 success (knowledge extended), 0 failure (key not in class),
// -1 skipped (nothing to learn / known impossible / over budget).
static int attack_sequence(const Seq& s,Knowledge& E,Oracle& O,std::mt19937_64& rng,int budget,int Nconf,AttackStats& st,bool verbose){
    // (a) key relations of the sequence against what is known
    Knowledge rel;                                   // unknown independent relations, local
    for(auto& kr:s.krel){ int val=0; KVec r=E.reduce(kr.first,&val);
        if(kzero(r)){ if(val!=kr.second){ st.seq_skipped++; return -1; } continue; }
        int a=rel.add(r,kr.second^val); if(a<0){ st.seq_skipped++; return -1; } }
    int u=rel.rank();
    // (b) the linear forms of the key that fix the tweak pattern, reduced by E
    struct LB { KVec v; uint64_t comb; }; std::vector<LB> basis; std::vector<KVec> gvec;   // local basis with combination tracking
    std::vector<int> kappa(s.trows.size()); std::vector<uint64_t> comb(s.trows.size());
    for(size_t r=0;r<s.trows.size();r++){
        int val=0; KVec rho=E.reduce(s.trows[r].k,&val); kappa[r]=val; uint64_t cm=0;
        for(auto& b:basis) if(kbit(rho,klow(b.v))){ kxor(rho,b.v); cm^=b.comb; }
        if(!kzero(rho)){ int d=(int)basis.size(); if(d>=63){ st.seq_skipped++; return -1; }
            int piv=klow(rho); for(auto& b:basis) if(kbit(b.v,piv)){ kxor(b.v,rho); b.comb^=1ull<<d; }
            basis.push_back({rho,1ull<<d}); gvec.push_back(rho); cm^=1ull<<d; }
        comb[r]=cm;
    }
    int d=(int)basis.size();
    if(d==0&&u==0){ st.seq_skipped++; return -1; }       // nothing new to learn
    if(d>budget){ st.seq_skipped++; return -1; }
    st.seq_tried++; st.log2patterns+= d;
    // (c) enumerate the 2^d patterns
    uint64_t pivmask=0; for(auto& tr:s.trows) pivmask|=(tr.tbits&-tr.tbits);
    long long q0=O.queries;
    for(uint64_t g=0; g<(1ull<<d); g++){
        uint64_t tb=0;
        for(size_t r=0;r<s.trows.size();r++){ const Seq::TRow& tr=s.trows[r]; uint64_t piv=tr.tbits&-tr.tbits;
            int v=tr.rhs^kappa[r]^__builtin_parityll(comb[r]&g); if(v) tb|=piv; }
        (void)pivmask;
        craft::Nib T; for(int j=0;j<16;j++) T[j]=(uint8_t)((tb>>(4*j))&15);
        int v0=-1; bool ok=true;
        for(int n=0;n<Nconf;n++){ craft::Nib p=random_nib(rng); craft::Nib c=O.enc(p,T); int v=I0(s,p)^Gc(s,c,32);
            if(v0<0) v0=v; else if(v!=v0){ ok=false; break; } }
        if(ok){
            for(int l=0;l<d;l++) E.add(gvec[l],(int)((g>>l)&1));
            for(auto& e:rel.rows) E.add(e.v,e.rhs);
            st.seq_success++; st.queries+=O.queries-q0;
            if(verbose) printf("  + %s  codim %d  guessed %2d bits  queries 2^%.1f  -> known rank %d\n",s.name().c_str(),s.codim(),d,std::log2((double)(O.queries-q0)),E.rank());
            return 1;
        }
    }
    st.seq_failed++; st.queries+=O.queries-q0;
    if(u==1){ E.add(rel.rows[0].v,rel.rows[0].rhs^1);     // the single unknown relation is false
        if(verbose) printf("  - %s  failed, learned the negated relation (rank %d)\n",s.name().c_str(),E.rank()); }
    else if(verbose) printf("  - %s  failed (codim %d, %d unknown relations)\n",s.name().c_str(),s.codim(),u);
    return 0;
}

// Run the whole library adaptively: cheapest sequences first, several passes.
static void run_attack(const std::vector<Seq>& L,Knowledge& E,Oracle& O,std::mt19937_64& rng,int budget,double log2_qbudget,AttackStats& st,bool verbose){
    std::vector<char> done(L.size(),0);           // a sequence is queried at most once per key
    for(int thr=0;thr<=budget;thr++){
        bool progress=true;
        while(progress){ progress=false;
            for(size_t q=0;q<L.size();q++){
                if(done[q]) continue;
                if(E.rank()>=64) return;
                if((double)st.queries>std::pow(2.0,log2_qbudget)) return;
                int before=E.rank();
                int r=attack_sequence(L[q],E,O,rng,thr,40,st,verbose);
                if(r>=0) done[q]=1;
                if(r>=0&&E.rank()>before) progress=true;
            }
        }
    }
}

// ----------------------------------------------------------------------------
// 7. Modes
// ----------------------------------------------------------------------------
static void print_conditions(const Seq& s){
    printf("sequence %s  (period %d)\n",s.name().c_str(),s.per);
    for(int t=0;t<4;t++){ printf("  TK%d:",t); for(int j=0;j<8;j++){ uint16_t ks=s.cond(t,j); if(ks==0xffff) continue; int i=craft::P[j];
        printf(" [%2d] in {",i); for(int k=0;k<16;k++) if((ks>>k)&1) printf("%x",k); printf("}"); } puts(""); }
    printf("  affine system: rank %d, T-pivots %d, pure key relations %d\n",s.rankT+s.codim(),s.rankT,s.codim());
    printf("  weak keys 2^%d, weak (key,tweak) pairs 2^%d, weak tweaks per weak key 2^%d\n",seq_logkeys(s),seq_logpairs(s),seq_logpairs(s)-seq_logkeys(s));
    for(auto& kr:s.krel){ printf("  relation: "); for(int c=0;c<128;c++) if(kbit(kr.first,c)) printf("%s[%d]_%d ",c<64?"K0":"K1",(c&63)/4,c&3); printf("= %d\n",kr.second); }
    // information available to a chosen-tweak attacker: rank of the key parts of the T-rows
    Knowledge K; for(auto& tr:s.trows) K.add(tr.k,0); for(auto& kr:s.krel) K.add(kr.first,0);
    int info=K.rank(); printf("  key information from the pattern test: %d linear bits (%d of which are the class relations), patterns 2^%d\n",info,s.codim(),info-s.codim());
}

static int mode_phase1(int nkeys,uint64_t seed){
    std::mt19937_64 rng(seed);
    std::vector<Seq> L=builtin_sequences(false);
    const Seq& s=L[0];
    print_conditions(s);
    puts("\n[phase 1] random keys in C127 = { <5,K0[9]> = <5,K1[9]> }, weak tweak built from the conditions, 64 plaintexts, all R = 1..32");
    int fail=0, total=0, gamma_obs=-1, gamma_mixed=0;
    // predicted constant gamma = xor_{t odd} <4,RCa[t]> + xor_{t even} <5,RCb[t]> + xor_{t odd} <2,RCb[t]>  (Theorem on the class, (iii))
    int gamma_pred=0; for(int t=0;t<32;t++){ if(t&1) gamma_pred^=par(4&craft::RCa[t])^par(2&craft::RCb[t]); else gamma_pred^=par(5&craft::RCb[t]); }
    for(int n=0;n<nkeys;n++){
        craft::Nib k0=random_nib(rng),k1=random_nib(rng);
        if(par(5&k0[9])!=par(5&k1[9])) k1[9]^=1;                 // force the class bit
        uint64_t key[2]; pack_key(k0,k1,key);
        craft::Nib T; if(!weak_tweak(s,key,rng,T)){ puts("  sampler error: key reported outside the class"); return 1; }
        craft::Tweakeys tk=craft::schedule(k0,k1,T);
        // check the conditions explicitly
        for(int t=0;t<4;t++) for(int j=0;j<8;j++){ uint16_t ks=s.cond(t,j); if(!((ks>>tk.tk[t][craft::P[j]])&1)){ puts("  sampler error: a condition is violated"); return 1; } }
        for(int R=1;R<=32;R++){ int v0=-1; bool c=true; for(int q=0;q<64;q++){ craft::Nib p=random_nib(rng); craft::Nib ct=craft::encrypt(p,tk,R); int v=I0(s,p)^Gc(s,ct,R); if(v0<0) v0=v; else if(v!=v0){c=false;break;} }
            total++; if(!c){ fail++; printf("  FAIL key %d R=%d\n",n,R); }
            if(R==32&&c){ if(gamma_obs<0) gamma_obs=v0; else if(gamma_obs!=v0) gamma_mixed=1; } }
    }
    printf("  invariant constant in %d/%d (key,R) cases\n",total-fail,total);
    printf("  32-round constant: observed %d%s, predicted from the round constants %d -> %s\n",gamma_obs,gamma_mixed?" (NOT the same for all keys!)":" (same for all keys)",gamma_pred,(gamma_obs==gamma_pred&&!gamma_mixed)?"ok":"MISMATCH");
    puts("[phase 1] negative controls at 32 rounds, 64 plaintexts each");
    int negc=0; for(int n=0;n<nkeys;n++){ craft::Nib k0=random_nib(rng),k1=random_nib(rng),T=random_nib(rng); craft::Tweakeys tk=craft::schedule(k0,k1,T);
        int v0=-1; bool c=true; for(int q=0;q<64&&c;q++){ craft::Nib p=random_nib(rng); craft::Nib ct=craft::encrypt(p,tk,32); int v=I0(s,p)^Gc(s,ct,32); if(v0<0) v0=v; else if(v!=v0) c=false; } negc+=c; }
    printf("  random (K,T): constant in %d/%d\n",negc,nkeys);
    int nm=0; for(int n=0;n<nkeys;n++){ craft::Nib k0=random_nib(rng),k1=random_nib(rng); if(par(5&k0[9])!=par(5&k1[9])) k1[9]^=1;
        uint64_t key[2]; pack_key(k0,k1,key); craft::Nib T; weak_tweak(s,key,rng,T); k1[9]^=1;   // leave the class, keep the tweak
        craft::Tweakeys tk=craft::schedule(k0,k1,T);
        int v0=-1; bool c=true; for(int q=0;q<64&&c;q++){ craft::Nib p=random_nib(rng); craft::Nib ct=craft::encrypt(p,tk,32); int v=I0(s,p)^Gc(s,ct,32); if(v0<0) v0=v; else if(v!=v0) c=false; } nm+=c; }
    printf("  near miss (class bit flipped, same tweak): constant in %d/%d\n",nm,nkeys);
    // out of class: no tweak at all should work; check the class test on random keys
    int inclass=0; for(int n=0;n<4096;n++){ craft::Nib k0=random_nib(rng),k1=random_nib(rng); uint64_t key[2]; pack_key(k0,k1,key); craft::Nib T; inclass+=weak_tweak(s,key,rng,T); }
    printf("  fraction of random keys in the class: %d/4096 (expected about 2048)\n",inclass);
    return fail?1:0;
}

// Print the true key as 128 bits, '*' for a bit not pinned down by the current
// knowledge E (i.e. the unit vector at that position is not in the row span).
static void print_key_bits(const Knowledge& E,const uint64_t key[2]){
    auto known=[&](int c)->int{ KVec v{}; v.w[c>>6]=1ull<<(c&63);
        int val=0; KVec r=E.reduce(v,&val); return kzero(r)? val : -1; };
    for(int half=0;half<2;half++){
        printf("  %s: ",half?"K1":"K0");
        // cell order must match craft::tohex: cell 0 printed first (left), cell 15 last (right).
        for(int i=0;i<=15;i++){ for(int b=3;b>=0;b--){ int c=64*half+4*i+b; int k=known(c); putchar(k<0?'*':('0'+k)); } putchar(' '); }
        putchar('\n');
    }
}

static int mode_v2(int nkeys,uint64_t seed,const std::vector<Seq>& lib,int budget,double qb){
    std::mt19937_64 rng(seed);
    std::vector<int> hist(65,0); double sumq=0; int ok=0;
    for(int n=0;n<nkeys;n++){
        Oracle O; O.k0=random_nib(rng); O.k1=random_nib(rng); pack_key(O.k0,O.k1,O.key);
        printf("\n==================== key %d ====================\n",n);
        printf("  secret key generated (the attack below never reads this line):\n");
        printf("    K0 = %s\n    K1 = %s\n",craft::tohex(O.k0).c_str(),craft::tohex(O.k1).c_str());
        printf("  searching the library for sequences this key satisfies ...\n");
        Knowledge E; AttackStats st;
        run_attack(lib,E,O,rng,budget,qb,st,nkeys<=4);
        bool cons=E.consistent_with(O.key);
        printf("%s key %2d: recovered %2d linear bits on the low key half, queries 2^%.2f, sequences tried %d (ok %d, failed %d, skipped %d), consistent with the true key: %s\n",
               cons?"[OK] ":"[!!] ",n,E.rank(),std::log2((double)std::max(1LL,O.queries)),st.seq_tried,st.seq_success,st.seq_failed,st.seq_skipped,cons?"yes":"NO");
        printf("  key bits pinned down by the attack (* = still unknown):\n");
        print_key_bits(E,O.key);
        hist[E.rank()]++; sumq+=(double)O.queries; ok+=cons;
        // The attack recovers E.rank() linear bits of the low key half from the
        // invariants alone, never reading the high key. The rest of the key, the
        // unrecovered low bits together with the 64 blind high bits, is one
        // exhaustive search, verified against a known plaintext/ciphertext pair.
        printf("  remaining search to finish the key: 2^%d, over the %d unrecovered low key bits and the 64 blind high key bits, verified against a known plaintext/ciphertext pair\n",
               128-E.rank(), 64-E.rank());
        printf("==================== end key %d ====================\n",n);
    }
    puts("\nhistogram of recovered low-key bits:"); for(int r=0;r<=64;r++) if(hist[r]) printf("  %2d bits : %d keys\n",r,hist[r]);
    printf("mean queries per key 2^%.2f; knowledge consistent with the true key in %d/%d keys\n",std::log2(sumq/nkeys),ok,nkeys);
    return 0;
}

static void usage(){
    puts("usage: craft_invattack selftest | conditions a0 a1 a2 a3 | phase1 [--keys N] [--seed s]\n"
         "       craft_invattack v2 [--keys N] [--seed s]                  (built-in 2^127 twin pair only)\n"
         "       craft_invattack attack [--lib f]... [--skeleton] [--keys N] [--budget d] [--qbudget log2] [--seed s]");
}

int main(int argc,char** argv){
    craft::init_constants(); build_kset();
    if(!craft::selftest()) return 1;
    if(!kset_selftest()) return 1;
    if(argc<2){ usage(); return 0; }
    std::string mode=argv[1];
    int keys=20, budget=16; uint64_t seed=0x1767; double qb=40; bool skel=false; bool seed_given=false; std::vector<std::string> libs;
    for(int i=2;i<argc;i++){ std::string a=argv[i];
        if(a=="--keys"&&i+1<argc) keys=atoi(argv[++i]); else if(a=="--seed"&&i+1<argc){ seed=strtoull(argv[++i],0,0); seed_given=true; }
        else if(a=="--budget"&&i+1<argc) budget=atoi(argv[++i]); else if(a=="--qbudget"&&i+1<argc) qb=atof(argv[++i]);
        else if(a=="--lib"&&i+1<argc) libs.push_back(argv[++i]);
        else if(a=="--skeleton") skel=true; }
    if(!seed_given){
        // Without --seed every run used the same hard-coded constant, so every
        // invocation produced exactly the same "random" keys. Draw a fresh seed
        // from real entropy instead, and print it so the run can be reproduced.
        std::random_device rd;
        seed = ((uint64_t)rd()<<32) ^ (uint64_t)rd()
             ^ (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count();
        printf("no --seed given: using fresh seed 0x%016llx (pass --seed 0x%llx to reproduce this run)\n",
               (unsigned long long)seed,(unsigned long long)seed);
    }
    if(mode=="selftest"){ puts("cipher test vector, S/P involutions and the free-triple table: ok"); return 0; }
    if(mode=="conditions"){ if(argc<6){ usage(); return 1; } std::string a[4]={argv[2],argv[3],argv[4],argv[5]}; Seq s; if(!parse_seq(s,a)){ puts("bad masks"); return 1; }
        analyse_seq(s); if(!s.valid){ puts("not an invariant sequence"); return 1; } print_conditions(s); return 0; }
    if(mode=="phase1") return mode_phase1(keys,seed);
    std::vector<Seq> L; if(libs.empty()) L=builtin_sequences(skel);   // built-in demo sequences only when no library file is given
    for(auto& f:libs){ int n=load_library(f.c_str(),L); printf("loaded %d sequences from %s\n",n,f.c_str()); }
    dedup_sort(L);
    printf("library: %zu sequences (period 1/2/4), codimension of the largest class %d\n",L.size(),L.empty()?-1:L.front().codim());
    if(mode=="v2"){ std::vector<Seq> twin; for(auto& s:L) if(s.codim()==1&&s.per==2&&s.rankT==34) twin.push_back(s); printf("twin pair: %zu sequences\n",twin.size()); return mode_v2(keys,seed,twin,24,40); }
    if(mode=="attack") return mode_v2(keys,seed,L,budget,qb);
    usage(); return 1;
}
