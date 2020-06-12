# A translator from AbC to C

Actions composed by process operators can be emulated, under
non-derterministic scheduling, by a sequential functions (in
sequential language like C) whose execution is guarded by proper
enable conditions.

System emulation is achived by an emulation loop, at each step
nondeterministically choosing one output action from the the set of enabling actions.

Properties of interests are currently expressed by using assert
statements. See the examples folder to encode the formula p. It is
possible to express bounded versions of safety, i.e., AG p or liveness
including AF p , AF (AG p), (EF p) within a number of emulation steps.

## Folder:

* src: translator code (in Erlang)
* examples: AbC specifications (or models) + generated, instrumented C files

## Backend supports (with changing the names of verification oriented primitives accordingly)

CBMC

ESBMC
