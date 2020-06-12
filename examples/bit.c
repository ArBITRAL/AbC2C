#define N N_Bit // # components


#define N_Bit 8 // # components (of this type)
#define NP_Bit 1 // # action indexes
#define NS_Bit 1 // # sending actions
#define NR_Bit 1 // # receiving actions

#define NP_MAX 1 // # max action indexes
#define ND_MAX 2 // # max process definitions
#define NV_MAX 1 // # bound variables (max)

#define true 1
#define false 0


typedef int (*pts)(int, int);
typedef int (*ptr)(int, int, int*);

struct {
  int ns;
  int nr;
  pts* SendAct;
  ptr* RecvAct;
} lookup[N];

int Evolve(int);
void Sync(int, int*);
void receive(int, int, int*);

int pc[N][NP_MAX] = {};

int bound[N][ND_MAX][NV_MAX];

// attributes
int ob[N];
int ib[N];

int tgt[N] = {};
unsigned short nondet_ushort();
_Bool nondet_bool();


// ---------- COMPONENT Bit ------------


// ----- Receive -----
int __Bit_b1(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Bit) {
    if (pc[_i][0] == 0 && (ib[_i] == 0) && (_m[0] == 1)) {
      bound[_i][0][0] = _m[0];
      //--- attr update ---
      ob[_i] = 1;

      pc[_i][0] = 1;
      return 1;
    }
  }
  return 0;
}

// ----- Send -----
int __Bit_a1(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Bit) {
    if (!_f)
      return (pc[_i][0] == 0 && (ib[_i] == 1));

    if (pc[_i][0] == 0 && (ib[_i] == 1)) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (ib[_j] == 0))
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = ib[_i];
      Sync(_i,_m);
      //--- attr update ---
    ob[_i] = 1;

      pc[_i][0] = 2;
      return 1;
    }
  }
  return 0;
}
// ---------- Action Table Bit ------------

pts st_Bit[] = {&__Bit_a1};

ptr rt_Bit[] = {&__Bit_b1};


// ---------- DRIVERS ------------
int Evolve(int _i) {
  pts* _sa = lookup[_i].SendAct;
  int _ns = lookup[_i].ns;
  unsigned short _k = nondet_ushort();
  __CPROVER_assume((_k >= 0) && (_k < _ns));
  return (_sa[_k])(_i,1);
}

void Sync(int _j, int* _m) {
  for (int _i = 0;  _i < N; _i++)
    if (tgt[_i]) {
      tgt[_i] = 0;
      receive(_i,_j,_m);
    }
}

void receive(int _i, int _j, int* _m) {
  ptr* _ra = lookup[_i].RecvAct;
  int _nr = lookup[_i].nr;
  for (int _k = 0; _k < _nr; _k++)
    if ((_ra[_k])(_i,_j,_m)) break;
}

int schedule() {
  unsigned short _i = nondet_ushort();
  __CPROVER_assume((_i >= 0) && (_i < N));
  return _i;
}

int available() {
  int _i,_k,_ns;
  pts* _sa;
  for (_i = 0; _i < N; _i ++) {
    _ns = lookup[_i].ns;
    _sa = lookup[_i].SendAct;
    for (_k = 0; _k < _ns; _k++)
      if ((_sa[_k])(_i,0))
	return 1;
  }
  return 0;
}

int input(int pre) {
  int i = nondet_bool();
  __CPROVER_assume(i >= pre);
  return i;
}


void init() {
  int _i, _j;
  ob[0] = 0;
  ib[0] = input(0);
  for (_i = 1;_i < N_Bit;_i++) {
    ob[_i] = 0;
    ib[_i] = input(ib[_i-1]);
  }

  for (_i = 0;_i < N_Bit;_i++) {
    lookup[_i].ns = NS_Bit;
    lookup[_i].nr = NR_Bit;
    lookup[_i].SendAct = st_Bit;
    lookup[_i].RecvAct = rt_Bit;}
}

//---Properties---
_Bool p0() {
  int re = 0, _i;
  for (_i =0; _i < N; _i++) {
    re = (re || ib[_i]);
  }
  for (_i =0; _i < N; _i++) {
    if (ob[_i] != re)
      return false;
  }
  return true;
}

int main() {
  init();
  int cnt = 0;
  unsigned short cid;
  _Bool live=false, saved=false;
  _Bool aa = available();
  while (aa) {
    cnt++;
    cid = schedule();
    __CPROVER_assume(Evolve(cid));
    aa = available();
    live = saved?(live && p0()):(live || p0());
    if (!saved && live) saved = true;
    __CPROVER_assert((!(cnt == 7) && aa)|| live, "");
  }
  return 0;
}
