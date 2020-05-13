#define N N_Phi // # components 


#define N_Phi 4 // # components (of this type) 
#define ND_Phi 1 // # process definitions 
#define NP_Phi 1 // # action indexes 
#define NS_Phi 4 // # sending actions 
#define NR_Phi 7 // # receiving actions 
#define NV_Phi 5 // # bound variables (max) 


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
int o[N];
int c[N];

int tgt[N] = {};
unsigned short nondet_ushort();
_Bool nondet_bool();


// ---------- COMPONENT Phi ------------ 
 
// ----- Send ----- 
int __Phi_a1(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (!_f)
      return (pc[_i][0] == 0);

    if (pc[_i][0] == 0) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[3];
      _m[0] = u[_i];
      _m[1] = o[_i];
      _m[2] = c[_i];
      Sync(_i,_m);

      pc[_i][0] = 1;
      return 1;
    }
  }
  return 0;
}

// ----- Receive ----- 
int __Phi_b1(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (pc[_i][0] == 1 && (u[_i] == _m[0] && c[_j] > c[_i])) {
      bound[_i][0][0] = _m[0];
      bound[_i][0][1] = _m[1];
      //--- attr update --- 
      o[_i] = bound[_i][0][1];

      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}


// ----- Receive ----- 
int __Phi_b2(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (pc[_i][0] == 1 && (u[_i] == _m[0] && c[_j] == c[_i])) {
      bound[_i][0][0] = _m[0];
      bound[_i][0][1] = _m[1];
      //--- attr update --- 
      o[_i] = 1;
    c[_i] = 0;

      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}


// ----- Receive ----- 
int __Phi_b3(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (pc[_i][0] == 1 && (u[_i] == _m[0] && c[_j] < c[_i])) {
      bound[_i][0][0] = _m[0];
      bound[_i][0][1] = _m[1];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}


// ----- Receive ----- 
int __Phi_b4(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (pc[_i][0] == 0 && (u[_i] != _m[0] && _m[1] == o[_i])) {
      bound[_i][0][0] = _m[0];
      bound[_i][0][1] = _m[1];
      bound[_i][0][2] = _m[2];
      pc[_i][0] = 2;
      return 1;
    }
  }
  return 0;
}


// ----- Receive ----- 
int __Phi_b5(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (pc[_i][0] == 2 && (bound[_i][0][0] == _m[0] && _m[1] != bound[_i][0][1])) {
      bound[_i][0][3] = _m[0];
      bound[_i][0][4] = _m[1];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}


// ----- Receive ----- 
int __Phi_b6(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (pc[_i][0] == 0 && (u[_i] != _m[0] && _m[1] != o[_i])) {
      bound[_i][0][0] = _m[0];
      bound[_i][0][1] = _m[1];
      bound[_i][0][2] = _m[2];
      pc[_i][0] = 3;
      return 1;
    }
  }
  return 0;
}
 
// ----- Send ----- 
int __Phi_a2(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (!_f)
      return (pc[_i][0] == 3 && (bound[_i][0][2] > c[_i]));

    if (pc[_i][0] == 3 && (bound[_i][0][2] > c[_i])) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[2];
      _m[0] = bound[_i][0][0];
      _m[1] = o[_i];
      Sync(_i,_m);
      //--- attr update --- 
    o[_i] = bound[_i][0][1];
      
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
} 
// ----- Send ----- 
int __Phi_a3(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (!_f)
      return (pc[_i][0] == 3 && (bound[_i][0][2] == c[_i]));

    if (pc[_i][0] == 3 && (bound[_i][0][2] == c[_i])) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[2];
      _m[0] = bound[_i][0][0];
      _m[1] = o[_i];
      Sync(_i,_m);
      //--- attr update --- 
    o[_i] = 1;
    c[_i] = 0;
      
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
} 
// ----- Send ----- 
int __Phi_a4(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (!_f)
      return (pc[_i][0] == 3 && (bound[_i][0][2] < c[_i]));

    if (pc[_i][0] == 3 && (bound[_i][0][2] < c[_i])) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[2];
      _m[0] = bound[_i][0][0];
      _m[1] = o[_i];
      Sync(_i,_m);

      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}

// ----- Receive ----- 
int __Phi_b7(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (pc[_i][0] == 3 && (bound[_i][0][0] == _m[0] && _m[1] != bound[_i][0][1])) {
      bound[_i][0][3] = _m[0];
      bound[_i][0][4] = _m[1];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}

// ---------- Action Table Phi ------------ 

pts st_Phi[] = {&__Phi_a1,&__Phi_a2,&__Phi_a3,&__Phi_a4};

ptr rt_Phi[] = {&__Phi_b1,&__Phi_b2,&__Phi_b3,&__Phi_b4,&__Phi_b5,&__Phi_b6,&__Phi_b7};


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


//----init A1 ----- 
void init0() {u[0] = 1; c[0] = 1; o[0] = 1;}

//----init A2 ----- 
void init1() {u[1] = 2; c[1] = 1; o[1] = 1;}

//----init A3 ----- 
void init2() {u[2] = 3; c[2] = 1; o[2] = 0;}

//----init A4 ----- 
void init3() {u[3] = 4; c[3] = 1; o[3] = 0;}


void init() {
  init0();
  init1();
  init2();
  init3();
  int _i, _j;
  for (_i = 0;_i < N_Phi;_i++) {
    lookup[_i].ns = NS_Phi;
    lookup[_i].nr = NR_Phi;
    lookup[_i].SendAct = st_Phi;
    lookup[_i].RecvAct = rt_Phi;
    pc[_i] = (int*) malloc(sizeof(int) * NP_Phi);
    bound[_i] = (int**) malloc(sizeof(int*) * ND_Phi);
    for (_j = 0; _j < ND_Phi; _j++) bound[_i][_j] = (int*) malloc(sizeof(int) * NV_Phi);
    for (_j = 0; _j < NP_Phi; _j++) pc[_i][_j] = 0;
   }
}

void clean() {
  int _i, _j;
  for (_i = 0;_i < N_Phi;_i++) {
    for (_j = 0; _j < ND_Phi; _j++) free(bound[_i][_j]);
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

