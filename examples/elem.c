#define N N_Elem // # components


#define N_Elem 10 // # components (of this type)
#define NP_Elem 2 // # action indexes
#define NS_Elem 1 // # sending actions
#define NR_Elem 1 // # receiving actions

#define NP_MAX 2 // # max action indexes
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
int s[N];
int n[N];

int tgt[N] = {};
unsigned short nondet_ushort();
_Bool nondet_bool();


// ---------- COMPONENT Elem ------------

// ----- Send -----
int __Elem_a1(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Elem) {
    if (!_f)
      return (pc[_i][0] == 0 && (s[_i] == 1));

    if (pc[_i][0] == 0 && (s[_i] == 1)) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (n[_j] <= n[_i]))
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = n[_i];
      Sync(_i,_m);

      pc[_i][0] = 1;
      return 1;
    }
  }
  return 0;
}

// ----- Receive -----
int __Elem_b1(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Elem) {
    if (pc[_i][1] == 0 && (_m[0] >= n[_i])) {
      bound[_i][1][0] = _m[0];
      //--- attr update ---
      s[_i] = 0;

      pc[_i][1] = 1;
      return 1;
    }
  }
  return 0;
}

// ---------- Action Table Elem ------------

pts st_Elem[] = {&__Elem_a1};

ptr rt_Elem[] = {&__Elem_b1};


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


//----init C1 -----
/* void init0() {s[0] = 1; n[0] = 1;} */

/* //----init C2 ----- */
/* void init1() {s[1] = 1; n[1] = 2;} */

/* //----init C3 ----- */
/* void init2() {s[2] = 1; n[2] = 3;} */

int input(int pre) {
  int i = nondet_ushort();
  __CPROVER_assume(i>= 1 && i <= N);
  return i;
}


void init() {
  /* init0(); */
  /* init1(); */
  /* init2(); */
  int _i, _j;
  s[0] = 1;
  n[0] = input(1);
  for (_i = 0; _i < N; _i++) {
    s[_i] = 1;
    n[_i] = input(n[_i - 1]);
  }

  for (_i = 0;_i < N_Elem;_i++) {
    lookup[_i].ns = NS_Elem;
    lookup[_i].nr = NR_Elem;
    lookup[_i].SendAct = st_Elem;
    lookup[_i].RecvAct = rt_Elem;}
}

//---Properties---
_Bool p0() {
  int sum = 0, f;
  for (int i=0; i < N; i++) {
    sum += s[i];
    if (s[i] == 1) f = i;
  }
   return (sum == 1 && s[f] == 1 && n[f] == N);
}

int main() {
  init();
  int cnt = 0;
  unsigned short cid;
  _Bool live=false, saved=false;
  _Bool aa = available();
  while (aa) {
    cnt ++;
    cid = schedule();
    __CPROVER_assume(Evolve(cid));
    aa = available();
    live = saved?(live && p0()):(live || p0());
    if (!saved && live) saved = true;
    __CPROVER_assert((!(cnt == 11) || aa) || live, "");
  }
  return 0;
}
