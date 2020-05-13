#define N N_Test // # components 


#define N_Test 2 // # components (of this type) 
#define ND_Test 3 // # process definitions 
#define NP_Test 3 // # action indexes 
#define NS_Test 2 // # sending actions 
#define NR_Test 3 // # receiving actions 
#define NV_Test 1 // # bound variables (max) 


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
int u[N];
int r[N];
int o[N];

int tgt[N] = {};
unsigned short nondet_ushort();
_Bool nondet_bool();


// ---------- COMPONENT Test ------------ 
 
// ----- Send ----- 
int __Test_a1(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Test) {
    if (!_f)
      return (pc[_i][0] == 0);

    if (pc[_i][0] == 0) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = r[_i];
      Sync(_i,_m);
      //--- attr update --- 
    r[_i] = 2;
      
      pc[_i][0] = 1;
      return 1;
    }
  }
  return 0;
}

// ----- Receive ----- 
int __Test_b1(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Test) {
    if (pc[_i][0] == 1 && pc[_i][1] == 0 && (u[_j] == _m[0] || r[_j] == r[_i])) {
      bound[_i][1][0] = _m[0];
      pc[_i][1] = 1;
      return 1;
    }
  }
  return 0;
}


// ----- Receive ----- 
int __Test_b2(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Test) {
    if (pc[_i][0] == 1 && pc[_i][2] == 0 && (u[_j] == _m[0] || r[_j] == r[_i])) {
      bound[_i][1][0] = _m[0];
      pc[_i][2] = 1;
      return 1;
    }
  }
  return 0;
}
 
// ----- Send ----- 
int __Test_a2(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Test) {
    if (!_f)
      return (pc[_i][0] == 0);

    if (pc[_i][0] == 0) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[2];
      _m[0] = o[_i];
      _m[1] = u[_i];
      Sync(_i,_m);

      pc[_i][0] = 2;
      return 1;
    }
  }
  return 0;
}

// ----- Receive ----- 
int __Test_b3(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Test) {
    if (pc[_i][0] == 2 && (u[_j] == _m[0] || r[_j] == r[_i])) {
      bound[_i][2][0] = _m[0];
      pc[_i][0] = 3;
      return 1;
    }
  }
  return 0;
}

// ---------- Action Table Test ------------ 

pts st_Test[] = {&__Test_a1,&__Test_a2};

ptr rt_Test[] = {&__Test_b1,&__Test_b2,&__Test_b3};


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


//----init T1 ----- 
void init0() {r[0] = 0;}

//----init T2 ----- 
void init1() {r[1] = 0;}


void init() {
  init0();
  init1();
  int _i, _j;
  for (_i = 0;_i < N_Test;_i++) {
    lookup[_i].ns = NS_Test;
    lookup[_i].nr = NR_Test;
    lookup[_i].SendAct = st_Test;
    lookup[_i].RecvAct = rt_Test;
    pc[_i] = (int*) malloc(sizeof(int) * NP_Test);
    bound[_i] = (int**) malloc(sizeof(int*) * ND_Test);
    for (_j = 0; _j < ND_Test; _j++) bound[_i][_j] = (int*) malloc(sizeof(int) * NV_Test);
    for (_j = 0; _j < NP_Test; _j++) pc[_i][_j] = 0;
   }
}

void clean() {
  int _i, _j;
  for (_i = 0;_i < N_Test;_i++) {
    for (_j = 0; _j < ND_Test; _j++) free(bound[_i][_j]);
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

