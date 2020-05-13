#define N N_Bit // # components 


#define N_Bit 3 // # components (of this type) 
#define ND_Bit 2 // # process definitions 
#define NP_Bit 1 // # action indexes 
#define NS_Bit 1 // # sending actions 
#define NR_Bit 1 // # receiving actions 
#define NV_Bit 1 // # bound variables (max) 


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
int o[N];
int i[N];

int tgt[N] = {};
unsigned short nondet_ushort();
_Bool nondet_bool();


// ---------- COMPONENT Bit ------------ 


// ----- Receive ----- 
int __Bit_b1(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Bit) {
    if (pc[_i][0] == 0 && (i[_i] == 0) && (_m[0] == 1)) {
      bound[_i][0][0] = _m[0];
      //--- attr update --- 
      o[_i] = 1;

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
      return (pc[_i][0] == 0 && (i[_i] == 1));

    if (pc[_i][0] == 0 && (i[_i] == 1)) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = i[_i];
      Sync(_i,_m);
      //--- attr update --- 
    o[_i] = 1;
      
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


//----init B1 ----- 
void init0() {i[0] = 1; o[0] = 0;}

//----init B2 ----- 
void init1() {i[1] = 0; o[1] = 0;}

//----init B3 ----- 
void init2() {i[2] = 0; o[2] = 0;}


void init() {
  init0();
  init1();
  init2();
  int _i, _j;
  for (_i = 0;_i < N_Bit;_i++) {
    lookup[_i].ns = NS_Bit;
    lookup[_i].nr = NR_Bit;
    lookup[_i].SendAct = st_Bit;
    lookup[_i].RecvAct = rt_Bit;
    pc[_i] = (int*) malloc(sizeof(int) * NP_Bit);
    bound[_i] = (int**) malloc(sizeof(int*) * ND_Bit);
    for (_j = 0; _j < ND_Bit; _j++) bound[_i][_j] = (int*) malloc(sizeof(int) * NV_Bit);
    for (_j = 0; _j < NP_Bit; _j++) pc[_i][_j] = 0;
   }
}

void clean() {
  int _i, _j;
  for (_i = 0;_i < N_Bit;_i++) {
    for (_j = 0; _j < ND_Bit; _j++) free(bound[_i][_j]);
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

