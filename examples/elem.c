#define N N_Elem // # components 


#define N_Elem 3 // # components (of this type) 
#define ND_Elem 2 // # process definitions 
#define NP_Elem 2 // # action indexes 
#define NS_Elem 1 // # sending actions 
#define NR_Elem 1 // # receiving actions 
#define NV_Elem 1 // # bound variables (max) 


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

int* pc[N];

int** bound[N];
	
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
        if (_j != _i && (true)) 
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
void init0() {s[0] = 1; n[0] = 1;}

//----init C2 ----- 
void init1() {s[1] = 1; n[1] = 2;}

//----init C3 ----- 
void init2() {s[2] = 1; n[2] = 3;}


void init() {
  init0();
  init1();
  init2();
  int _i, _j;
  for (_i = 0;_i < N_Elem;_i++) {
    lookup[_i].ns = NS_Elem;
    lookup[_i].nr = NR_Elem;
    lookup[_i].SendAct = st_Elem;
    lookup[_i].RecvAct = rt_Elem;
    pc[_i] = (int*) malloc(sizeof(int) * NP_Elem);
    bound[_i] = (int**) malloc(sizeof(int*) * ND_Elem);
    for (_j = 0; _j < ND_Elem; _j++) bound[_i][_j] = (int*) malloc(sizeof(int) * NV_Elem);
    for (_j = 0; _j < NP_Elem; _j++) pc[_i][_j] = 0;
   }
}

void clean() {
  int _i, _j;
  for (_i = 0;_i < N_Elem;_i++) {
    for (_j = 0; _j < ND_Elem; _j++) free(bound[_i][_j]);
    free(pc[_i]);
    free(bound[_i]);
  }    
}

//---Properties--- 
void check_safety() {
  _Bool safety = false;
  __CPROVER_assert(!safety,"");
}

void check_liveness() {
  _Bool liveness = true;
  __CPROVER_assert(liveness,"");
}


int main() {
  init();
  unsigned short cid;
  while (available()) {
    cid = schedule();
    __CPROVER_assume(Evolve(cid));
    check_safety();
  }
  check_liveness();
  clean();
  return 0;
}

