#define N_Follower 5 // # components (of this type)
#define NP_Follower 1 // # action indexes
#define NS_Follower 1 // # sending actions
#define NR_Follower 2 // # receiving actions

#define N_Dancer 3 // # components (of this type)
#define NP_Dancer 1 // # action indexes
#define NS_Dancer 1 // # sending actions
#define NR_Dancer 3 // # receiving actions

#define N N_Follower + N_Dancer // # components

#define NP_MAX 1 // # max action indexes
#define ND_MAX 1 // # max process definitions
#define NV_MAX 2 // # bound variables (max)

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
int u[N];
int r[N];
int p[N];

int tgt[N] = {};
unsigned short nondet_ushort();
_Bool nondet_bool();


// ---------- COMPONENT Dancer ------------

// ----- Send -----
int __Dancer_a1(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Dancer) {
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
int __Dancer_b1(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Dancer) {
    if (pc[_i][0] == 1 && (_m[0] == u[_i])) {
      bound[_i][0][0] = _m[0];
      //--- attr update ---
      p[_i] = 1;

      pc[_i][0] = 2;
      return 1;
    }
  }
  return 0;
}


// ----- Receive -----
int __Dancer_b2(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Dancer) {
    if (pc[_i][0] == 0 && (r[_j] == r[_i])) {
      bound[_i][0][0] = _m[0];
      pc[_i][0] = 3;
      return 1;
    }
  }
  return 0;
}


// ----- Receive -----
int __Dancer_b3(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Dancer) {
    if (pc[_i][0] == 3 && (_m[0] != u[_i])) {
      bound[_i][0][1] = _m[0];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}

// ---------- COMPONENT Follower ------------


// ----- Receive -----
int __Follower_b1(int _i, int _j, int* _m) {
  if (_i >= N_Dancer &&  _i < N_Follower + N_Dancer) {
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
  if (_i >= N_Dancer &&  _i < N_Follower + N_Dancer) {
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
    p[_i] = 1;

      pc[_i][0] = 2;
      return 1;
    }
  }
  return 0;
}

// ----- Receive -----
int __Follower_b2(int _i, int _j, int* _m) {
  if (_i >= N_Dancer &&  _i < N_Follower + N_Dancer) {
    if (pc[_i][0] == 1 && (_m[0] == bound[_i][0][0] && r[_j] == r[_i])) {
      bound[_i][0][1] = _m[0];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}

// ---------- Action Table Dancer ------------

pts st_Dancer[] = {&__Dancer_a1};

ptr rt_Dancer[] = {&__Dancer_b1,&__Dancer_b2,&__Dancer_b3};


// ---------- Action Table Follower ------------

pts st_Follower[] = {&__Follower_a1};

ptr rt_Follower[] = {&__Follower_b1,&__Follower_b2};


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


/* //----init C1 ----- */
/* void init0() {u[0] = 1; p[0] = 0; r[0] = 1;} */

/* //----init C2 ----- */
/* void init1() {u[1] = 2; p[1] = 0; r[1] = 1;} */

/* //----init C3 ----- */
/* void init2() {u[2] = 3; p[2] = 0; r[2] = 1;} */

/* //----init C4 ----- */
/* void init3() {u[3] = 4; p[3] = 0; r[3] = 1;} */

/* //----init C5 ----- */
/* void init4() {u[4] = 5; p[4] = 0; r[4] = 0;} */

/* void init5() {u[5] = 6; p[5] = 0; r[5] = 0;} */

/* void init6() {u[6] = 7; p[6] = 0; r[6] = 0;} */

/* void init7() {u[7] = 8; p[7] = 0; r[7] = 0;} */

/* void init8() {u[8] = 9; p[8] = 0; r[8] = 0;} */

/* void init9() {u[9] = 10; p[9] = 0; r[9] = 0;} */


void init() {
  /* init0(); */
  /* init1(); */
  /* init2(); */
  /* init3(); */
  /* init4(); */
  /* init5(); */
  /* init6(); */
  /* init7(); */
  /* init8(); */
  /* init9(); */
  int _i, _j;
  for (_i = 0;_i < N;_i++) {
    u[_i] = _i + 1;
    p[_i] = 0;
  }
  for (_i = N_Dancer;_i < N_Follower + N_Dancer;_i++) {
    r[_i] = 0;
    lookup[_i].ns = NS_Follower;
    lookup[_i].nr = NR_Follower;
    lookup[_i].SendAct = st_Follower;
    lookup[_i].RecvAct = rt_Follower;}
  for (_i = 0;_i < N_Dancer;_i++) {
    r[_i] = 1;
    lookup[_i].ns = NS_Dancer;
    lookup[_i].nr = NR_Dancer;
    lookup[_i].SendAct = st_Dancer;
    lookup[_i].RecvAct = rt_Dancer;}
}

//---Properties---
_Bool p0() {
  int d = 0, f = 0, i;
  for (i = 0; i < N; i++)
    if (r[i]) d += p[i]; else f += p[i];
  return ((d <= N_Dancer - 1) || (d == N_Dancer && f == N_Follower && d == f));
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
    __CPROVER_assert((!(cnt == 6) && aa)  || live, "");
  }
  return 0;
}
