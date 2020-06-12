# A translator that can translate AbC specifications to sequential C programs

Actions composed by process operators can be emulated, under
non-derterministic scheduling, by a sequential functions (in
sequential language like C) whose execution is guarded by proper
enable conditions.

Emulation of a system is achived via an emulation loop; at each step,
nondeterministically choosing one output action from the the set of
enabling output actions.

# Properties Instrumentation
Formula p representing wanted system states, are expressed by usual
boolean-valued functions/expressions in C

See the examples folder for details on how to express bounded versions
of safety, i.e., AG p or liveness including AF p, AF (AG p), (EF p)
via assertions.

If a verification suceeds, the result means that the considered
property is valid within a number of steps of system's evolution.

## Folder:

* src: translator code (in Erlang)
* examples: AbC specifications (or models) + generated, instrumented C files

## Backends
Tested with
1. CBMC
2. ESBMC
