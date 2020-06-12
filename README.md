# A translator from AbC to C

Actions composed by process operators can be sequentialized in
sequential language by setting proper enabled and disabled conditions
over corresponding C functions.

System emulation is achived by nondetermistic scheduling of the set of
enabled functions.

Properties of interests are currently expressed by using assert
statements. See the examples folder to encode the properties p. It is
possible to express safety, i.e., G p, or liveness, i.e., F p , F G p
within a number of execution steps.

## Folder:

* src: translator code (in Erlang)
* examples: AbC specifications (or models) + generated, instrumented C files

## Backend:

ESBMC: for safety and termination analysis
CBMC: for safety and bounded liveness analysis
