#define N N_Follower + N_Leader // # components 


#define N_Leader 2 // # components (of this type) 
#define ND_Leader 2 // # process definitions 
#define NP_Leader 2 // # action indexes 
#define NS_Leader 1 // # sending actions 
#define NR_Leader 3 // # receiving actions 
#define NV_Leader 2 // # bound variables (max) 


#define N_Follower 3 // # components (of this type) 
#define ND_Follower 1 // # process definitions 
#define NP_Follower 1 // # action indexes 
#define NS_Follower 5 // # sending actions 
#define NR_Follower 6 // # receiving actions 
#define NV_Follower 2 // # bound variables (max) 


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


// ---------- COMPONENT Leader ------------ 
 
// ----- Send ----- 
int __Leader_a1(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Leader) {
    if (!_f)
      return (pc[_i][0] == 0);

    if (pc[_i][0] == 0) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = u[_i];
      Sync(_i,_m);

      pc[_i][0] = 1;
      return 1;
    }
  }
  return 0;
}

// ----- Receive ----- 
int __Leader_b1(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Leader) {
    if (pc[_i][0] == 0 && (r[_j] == r[_i])) {
      bound[_i][0][0] = _m[0];
      pc[_i][0] = 2;
      return 1;
    }
  }
  return 0;
}


// ----- Receive ----- 
int __Leader_b2(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Leader) {
    if (pc[_i][0] == 2 && (_m[0] != u[_i])) {
      bound[_i][0][1] = _m[0];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}


// ----- Receive ----- 
int __Leader_b3(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Leader) {
    if (pc[_i][1] == 0 && (_m[0] == u[_i])) {
      bound[_i][1][0] = _m[0];
      //--- attr update --- 
      o[_i] = 1;

      pc[_i][1] = 1;
      return 1;
    }
  }
  return 0;
}

// ---------- COMPONENT Follower ------------ 


// ----- Receive ----- 
int __Follower_b1(int _i, int _j, int* _m) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (pc[_i][0] == 0 && (r[_j] != r[_i])) {
      bound[_i][0][0] = _m[0];
      pc[_i][0] = 1;
      return 1;
    }
  }
  return 0;
}
 
// ----- Send ----- 
int __Follower_a1(int _i, int _f) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (!_f)
      return (pc[_i][0] == 1);

    if (pc[_i][0] == 1) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = bound[_i][0][0];
      Sync(_i,_m);
      //--- attr update --- 
    o[_i] = 1;
      
      pc[_i][0] = 2;
      return 1;
    }
  }
  return 0;
}

// ----- Receive ----- 
int __Follower_b2(int _i, int _j, int* _m) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (pc[_i][0] == 1 && (_m[0] == bound[_i][0][0] && r[_j] == r[_i])) {
      bound[_i][0][1] = _m[0];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}
 
// ----- Send ----- 
int __Follower_a2(int _i, int _f) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (!_f)
      return (pc[_i][0] == 1);

    if (pc[_i][0] == 1) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = bound[_i][0][0];
      Sync(_i,_m);
      //--- attr update --- 
    o[_i] = 1;
      
      pc[_i][0] = 3;
      return 1;
    }
  }
  return 0;
}

// ----- Receive ----- 
int __Follower_b3(int _i, int _j, int* _m) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (pc[_i][0] == 1 && (_m[0] == bound[_i][0][0] && r[_j] == r[_i])) {
      bound[_i][0][1] = _m[0];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}
 
// ----- Send ----- 
int __Follower_a3(int _i, int _f) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (!_f)
      return (pc[_i][0] == 1);

    if (pc[_i][0] == 1) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = bound[_i][0][0];
      Sync(_i,_m);
      //--- attr update --- 
    o[_i] = 1;
      
      pc[_i][0] = 4;
      return 1;
    }
  }
  return 0;
}

// ----- Receive ----- 
int __Follower_b4(int _i, int _j, int* _m) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (pc[_i][0] == 1 && (_m[0] == bound[_i][0][0] && r[_j] == r[_i])) {
      bound[_i][0][1] = _m[0];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}
 
// ----- Send ----- 
int __Follower_a4(int _i, int _f) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (!_f)
      return (pc[_i][0] == 1);

    if (pc[_i][0] == 1) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = bound[_i][0][0];
      Sync(_i,_m);
      //--- attr update --- 
    o[_i] = 1;
      
      pc[_i][0] = 5;
      return 1;
    }
  }
  return 0;
}

// ----- Receive ----- 
int __Follower_b5(int _i, int _j, int* _m) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (pc[_i][0] == 1 && (_m[0] == bound[_i][0][0] && r[_j] == r[_i])) {
      bound[_i][0][1] = _m[0];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}
 
// ----- Send ----- 
int __Follower_a5(int _i, int _f) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (!_f)
      return (pc[_i][0] == 1);

    if (pc[_i][0] == 1) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true)) 
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = bound[_i][0][0];
      Sync(_i,_m);
      //--- attr update --- 
    o[_i] = 1;
      
      pc[_i][0] = 6;
      return 1;
    }
  }
  return 0;
}

// ----- Receive ----- 
int __Follower_b6(int _i, int _j, int* _m) {
  if (_i >= N_Leader &&  _i < N_Follower + N_Leader) {
    if (pc[_i][0] == 1 && (_m[0] == bound[_i][0][0] && r[_j] == r[_i])) {
      bound[_i][0][1] = _m[0];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}

// ---------- Action Table Leader ------------ 

pts st_Leader[] = {&__Leader_a1};

ptr rt_Leader[] = {&__Leader_b1,&__Leader_b2,&__Leader_b3};


// ---------- Action Table Follower ------------ 

pts st_Follower[] = {&__Follower_a1,&__Follower_a2,&__Follower_a3,&__Follower_a4,&__Follower_a5};

ptr rt_Follower[] = {&__Follower_b1,&__Follower_b2,&__Follower_b3,&__Follower_b4,&__Follower_b5,&__Follower_b6};


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
void init0() {u[0] = 1; o[0] = 0; r[0] = 1;}

//----init C2 ----- 
void init1() {u[1] = 2; o[1] = 0; r[1] = 1;}

//----init C3 ----- 
void init2() {u[2] = 3; o[2] = 0; r[2] = 1;}

//----init C4 ----- 
void init3() {u[3] = 4; o[3] = 0; r[3] = 0;}

//----init C5 ----- 
void init4() {u[4] = 5; o[4] = 0; r[4] = 0;}


void init() {
  init0();
  init1();
  init2();
  init3();
  init4();
  int _i, _j;
  for (_i = 0;_i < N_Leader;_i++) {
    lookup[_i].ns = NS_Leader;
    lookup[_i].nr = NR_Leader;
    lookup[_i].SendAct = st_Leader;
    lookup[_i].RecvAct = rt_Leader;
    pc[_i] = (int*) malloc(sizeof(int) * NP_Leader);
    bound[_i] = (int**) malloc(sizeof(int*) * ND_Leader);
    for (_j = 0; _j < ND_Leader; _j++) bound[_i][_j] = (int*) malloc(sizeof(int) * NV_Leader);
    for (_j = 0; _j < NP_Leader; _j++) pc[_i][_j] = 0;
   }
  for (_i = N_Leader;_i < N_Follower + N_Leader;_i++) {
    lookup[_i].ns = NS_Follower;
    lookup[_i].nr = NR_Follower;
    lookup[_i].SendAct = st_Follower;
    lookup[_i].RecvAct = rt_Follower;
    pc[_i] = (int*) malloc(sizeof(int) * NP_Follower);
    bound[_i] = (int**) malloc(sizeof(int*) * ND_Follower);
    for (_j = 0; _j < ND_Follower; _j++) bound[_i][_j] = (int*) malloc(sizeof(int) * NV_Follower);
    for (_j = 0; _j < NP_Follower; _j++) pc[_i][_j] = 0;
   }
}

void clean() {
  int _i, _j;
  for (_i = 0;_i < N_Leader;_i++) {
    for (_j = 0; _j < ND_Leader; _j++) free(bound[_i][_j]);
    free(pc[_i]);
    free(bound[_i]);
  }    
  for (_i = N_Leader;_i < N_Follower + N_Leader;_i++) {
    for (_j = 0; _j < ND_Follower; _j++) free(bound[_i][_j]);
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

