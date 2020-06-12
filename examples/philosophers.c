#include<stdio.h>
#define N N_Phi // # components

#define N_Phi 4 // # components (of this type)
#define NP_Phi 2 // # action indexes
#define NS_Phi 3 // # sending actions
#define NR_Phi 6 // # receiving actions

#define NP_MAX 2 // # max action indexes
#define ND_MAX 2 // # max process definitions

#define NV_MAX 3 // # bound variables (max)

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
int o[N];
int c[N];
int cnt = 0;
int tgt[N] = {};
unsigned short nondet_ushort();
_Bool nondet_bool();


// ---------- COMPONENT Phi ------------

// ----- Send -----
int __Phi_a1(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (!_f)
      return (pc[_i][0] == 0 && (o[_i] == 1));

    if (pc[_i][0] == 0 && (o[_i] == 1)) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true))
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      printf("\n\n ROUND %d, PHIL %d (o = %d, c = %d) starts \n\n",cnt,u[_i],o[_i],c[_i]);

      int _m[2];
      _m[0] = u[_i];
      _m[1] = c[_i];
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
    if (pc[_i][0] == 1 && (u[_i] == _m[0] && _m[1] != c[_i])) {
      bound[_i][0][0] = _m[0];
      bound[_i][0][1] = _m[1];
      //--- attr update ---
      o[_i] = c[_i];

      printf("\n\n ROUND %d, PHIL %d (o = %d, c = %d) -> (o = %d,c = %d) \n\n",cnt,u[_i],o[_i],c[_i],o[_i],c[_i]);
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}


// ----- Receive -----
int __Phi_b2(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (pc[_i][0] == 1 && (u[_i] == _m[0] && _m[1] == c[_i])) {
      printf("\n\n ROUND %d, PHIL %d (o = %d, c = %d) -> (o = %d, c = 0) \n\n",cnt,u[_i],o[_i],c[_i],o[_i]);
      bound[_i][0][0] = _m[0];
      bound[_i][0][1] = _m[1];
      //--- attr update ---
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
    if (pc[_i][0] == 0 && (o[_i] == 1 && o[_j] == o[_i])) {
      bound[_i][0][0] = _m[0];
      bound[_i][0][1] = _m[1];
      pc[_i][0] = 2;
      return 1;
    }
  }
  return 0;
}


// ----- Receive -----
int __Phi_b4(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (pc[_i][0] == 2 && (o[_j] != o[_i])) {
      bound[_i][0][0] = _m[0];
      bound[_i][0][1] = _m[1];
      pc[_i][0] = 0;
      return 1;
    }
  }
  return 0;
}


// ----- Receive -----
int __Phi_b5(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (pc[_i][1] == 0 && (o[_i] == 0) && (o[_j] != o[_i])) {
      bound[_i][1][0] = _m[0];
      bound[_i][1][1] = _m[1];
      pc[_i][1] = 1;
      printf("\n\n ROUND %d, PHIL %d (o = %d, c = %d) receives debate by %d \n\n",cnt,u[_i],o[_i],c[_i],u[_j]);
      return 1;
    }
  }
  return 0;
}

// ----- Send -----
int __Phi_a2(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (!_f)
      return (pc[_i][1] == 1 && (bound[_i][1][1] != c[_i]));

    if (pc[_i][1] == 1 && (bound[_i][1][1] != c[_i])) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true))
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;

      printf("\n\n ROUND %d, PHIL %d (o = %d, c = %d) -> (o = %d, c = %d) \n\n",cnt,u[_i],o[_i],c[_i],bound[_i][1][1],c[_i]);
      int _m[2];
      _m[0] = bound[_i][1][0];
      _m[1] = c[_i];
      Sync(_i,_m);
      //--- attr update ---
    o[_i] = bound[_i][1][1];

      pc[_i][1] = 0;
      return 1;
    }
  }
  return 0;
}
// ----- Send -----
int __Phi_a3(int _i, int _f) {
  if (_i >= 0 &&  _i < N_Phi) {
    if (!_f)
      return (pc[_i][1] == 1 && (bound[_i][1][1] == c[_i]));

    if (pc[_i][1] == 1 && (bound[_i][1][1] == c[_i])) {
      for (int _j= 0; _j < N; _j++)
        if (_j != _i && (true))
	  tgt[_j] = 1;
	else
	  tgt[_j] = 0;
      printf("\n\n ROUND %d, PHIL %d (o = %d, c = %d) -> (o = %d, c = 0) \n\n",cnt,u[_i],o[_i],c[_i],bound[_i][1][0], c[_i]);
      int _m[2];
      _m[0] = bound[_i][1][0];
      _m[1] = c[_i];
      Sync(_i,_m);
      //--- attr update ---
    o[_i] = 1;
    c[_i] = 0;

      pc[_i][1] = 0;
      return 1;
    }
  }
  return 0;
}

// ----- Receive -----
int __Phi_b6(int _i, int _j, int* _m) {
  if (_i >= 0 &&  _i < N_Phi) {
    //     printf("\n\n ROUND %d, PHIL %d (o = %d, c = %d) premtemped by %d \n\n",cnt,u[_i],o[_i],_j);
    if (pc[_i][1] == 1 && (_m[0] == bound[_i][1][0])) {
      bound[_i][1][2] = _m[0];
      bound[_i][1][1] = _m[1];
      pc[_i][1] = 0;
      return 1;
    }
  }
  return 0;
}

// ---------- Action Table Phi ------------

pts st_Phi[] = {&__Phi_a1,&__Phi_a2,&__Phi_a3};

ptr rt_Phi[] = {&__Phi_b1,&__Phi_b2,&__Phi_b3,&__Phi_b4,&__Phi_b5,&__Phi_b6};


// ---------- DRIVERS ------------
int Evolve(int _i) {
  pts* _sa = lookup[_i].SendAct;
  int _ns = NS_Phi; //lookup[_i].ns;
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
  int _nr = NR_Phi; //lookup[_i].nr;
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
    _ns = NS_Phi;//lookup[_i].ns;
    _sa = lookup[_i].SendAct;
    for (_k = 0; _k < _ns; _k++)
      if ((_sa[_k])(_i,0))
	return 1;
  }
  return 0;
}


void init() {
  o[0] = nondet_bool(); c[0] = 1;
  o[1] = nondet_bool(); c[1] = 1;
  o[2] = nondet_bool(); c[2] = 1;
  o[3] = nondet_bool(); c[3] = 1;

   __CPROVER_assume(o[0] + o[1] + o[2] + o[3] == 2);

  int _i, _j;
  for (_i = 0;_i < N_Phi;_i++) {
    u[_i] = _i + 1;
    //    c[_i] = 0;
    lookup[_i].ns = NS_Phi;
    lookup[_i].nr = NR_Phi;
    lookup[_i].SendAct = st_Phi;
    lookup[_i].RecvAct = rt_Phi;}
}

//---Properties---
_Bool p0() {
  int s1 = 0;
  for (int i = 0; i < N; i++)
    if (o[i]) s1++;
  return (s1 >= (N - s1));
}


//---Properties---

int main() {
 init();
  unsigned short cid;
  _Bool live=false,saved=false;
  _Bool aa = available();
  while (aa) {
    cnt ++;
    cid = schedule();
    __CPROVER_assume(Evolve(cid));
    aa = available();
    live = saved?(live && p0()):(live || p0());
    if (!saved && live) saved = true;
    __CPROVER_assert((!(cnt == 4) && aa) || live, "");
  }
  return 0;
}
