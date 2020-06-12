#define N N_Participant + N_Manager // # components

#define N_Participant 6 // # components (of this type)
#define NP_Participant 1 // # action indexes
#define NS_Participant 1 // # sending actions
#define NR_Participant 3 // # receiving actions

#define N_Manager 1 // # components (of this type)
#define NP_Manager 2 // # action indexes
#define NS_Manager 3 // # sending actions
#define NR_Manager 2 // # receiving actions

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
int r[N];
int v[N];
int c[N];
int d[N];
int n[N];

int tgt[N] = {};
unsigned short nondet_ushort();
_Bool nondet_bool();


// ---------- COMPONENT Manager ------------

// ----- Send -----
int __Manager_a1(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Manager) {
    if (!_f)
      return (pc[_i][0] == 0);

    if (pc[_i][0] == 0) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (r[_j] == 0))
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = 2;
      Sync(_i,_m);

      pc[_i][0] = 1;
      return 1;
    }
  }
  return 0;
}

// ----- Receive -----
int __Manager_b1(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Manager) {
    if (pc[_i][1] == 0 && (c[_i] < n[_i]) && (_m[0] == 1)) {
      bound[_i][1][0] = _m[0];
      //--- attr update ---
      c[_i] = c[_i]+1;
      pc[_i][1] = 0;
      return 1;
    }
  }
  return 0;
}


// ----- Receive -----
int __Manager_b2(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Manager) {
    if (pc[_i][1] == 0 && (c[_i] < n[_i]) && (_m[0] == 0)) {
      bound[_i][1][0] = _m[0];
      pc[_i][1] = 1;
      return 1;
    }
  }
  return 0;
}

// ----- Send -----
int __Manager_a2(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Manager) {
    if (!_f)
      return (pc[_i][1] == 1);

    if (pc[_i][1] == 1) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (r[_j] == 0))
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = 0;
      Sync(_i,_m);

      pc[_i][1] = 2;
      return 1;
    }
  }
  return 0;
}
// ----- Send -----
int __Manager_a3(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Manager) {
    if (!_f)
      return (pc[_i][1] == 0 && (c[_i] == n[_i]));

    if (pc[_i][1] == 0 && (c[_i] == n[_i])) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (r[_j] == 0))
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = 1;
      Sync(_i,_m);

      pc[_i][1] = 3;
      return 1;
    }
  }
  return 0;
}
// ---------- COMPONENT Participant ------------


// ----- Receive -----
int __Participant_b1(int _i, int _j, int* _m) {
  if (_i >= N_Manager &&  _i < N_Participant + N_Manager) {
    if (pc[_i][0] == 0 && (r[_j] == 1 && _m[0] == 2)) {
      bound[_i][0][0] = _m[0];
      pc[_i][0] = 1;
      return 1;
    }
  }
  return 0;
}

// ----- Send -----
int __Participant_a1(int _i, int _f) {
  if (_i >= N_Manager &&  _i < N_Participant + N_Manager) {
    if (!_f)
      return (pc[_i][0] == 1);

    if (pc[_i][0] == 1) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (r[_j] == 1))
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      int _m[1];
      _m[0] = v[_i];
      Sync(_i,_m);

      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}

// ----- Receive -----
int __Participant_b2(int _i, int _j, int* _m) {
  if (_i >= N_Manager &&  _i < N_Participant + N_Manager) {
    if (pc[_i][0] == 1 && (r[_j] == 1 && _m[0] != 2)) {
      bound[_i][0][0] = _m[0];
      //--- attr update ---
      d[_i] = bound[_i][0][0];
      pc[_i][0] = 2;
      return 1;
    }
  }
  return 0;
}


// ----- Receive -----
int __Participant_b3(int _i, int _j, int* _m) {
  if (_i >= N_Manager &&  _i < N_Participant + N_Manager) {
    if (pc[_i][0] == 0 && (r[_j] == 1 && _m[0] != 2)) {
      bound[_i][0][0] = _m[0];
      //--- attr update ---
      d[_i] = bound[_i][0][0];

      pc[_i][0] = 3;
      return 1;
    }
  }
  return 0;
}

// ---------- Action Table Manager ------------

pts st_Manager[] = {&__Manager_a1,&__Manager_a2,&__Manager_a3};

ptr rt_Manager[] = {&__Manager_b1,&__Manager_b2};


// ---------- Action Table Participant ------------

pts st_Participant[] = {&__Participant_a1};

ptr rt_Participant[] = {&__Participant_b1,&__Participant_b2,&__Participant_b3};


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
      if ((_sa[_k])(_i,0)) {
	return 1;
      }
  }
  return 0;
}

int input(int pre) {
  int i = nondet_bool();
   __CPROVER_assume(i >= pre);
  return i;
}


//----init C1 -----
void init0() {n[0] = N_Participant; c[0] = 0; r[0] = 1;}

void init() {
  init0();
  int _i, _j;
  v[N_Manager] = input(0);
  r[N_Manager] = 0;
  d[N_Manager] = -1;
  for (_i = N_Manager + 1;_i < N_Participant + N_Manager;_i++) {
    v[_i] = input(v[_i - 1]);
    r[_i] = 0;
    d[_i] = -1;
  }
  for (_i = N_Manager;_i < N_Participant + N_Manager;_i++) {
    lookup[_i].ns = NS_Participant;
    lookup[_i].nr = NR_Participant;
    lookup[_i].SendAct = st_Participant;
    lookup[_i].RecvAct = rt_Participant;}
  for (_i = 0;_i < N_Manager;_i++) {
    lookup[_i].ns = NS_Manager;
    lookup[_i].nr = NR_Manager;
    lookup[_i].SendAct = st_Manager;
    lookup[_i].RecvAct = rt_Manager;}
}

int sum() {
  int s = 0;
  for (int i = N_Manager;i < N_Participant + N_Manager; i ++) {
    s += d[i];
  }
  return s;
}

//---Properties---
_Bool p0() {
  int s = sum();
  return (s == 0 || (s == c[0] && s == n[0]));
}

int main() {
  init();
  unsigned short cid;
  int cnt = 0;
  _Bool live=false, saved=false;
  _Bool aa = available();
  while (available()) {
    cnt++;
    cid = schedule();
    __CPROVER_assume(Evolve(cid));
    aa = available();
    live = saved?(live && p0()):(live || p0());
    if (!saved && live) saved = true;
    __CPROVER_assert((!(cnt == 7) && aa) || live, "");
  }
  return 0;
}
