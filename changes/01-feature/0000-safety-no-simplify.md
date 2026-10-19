- `jasmin2ec --model safety` accepts `--no-safety-simplify`: the instrumented
  program is extracted without the final constant propagation and dead-code
  elimination, and the order of the initialisations of its init-tracking
  variables, the numbering of its variables and its auxiliary variables are
  made independent of array sizes, so that the shape of the extraction does not
  depend on the values of `param` declarations (needed for parametric safety
  proofs). With `--safety-simplify-from=IDENT` (repeatable), the functions
  defined in files reached through the include `IDENT` (of `-I IDENT=path`)
  nevertheless keep the standard treatment, so that their extraction matches
  the one of a library extracted without the flag (e.g. to reuse its safety
  models).
- `jasmin2ec --model safety` accepts `--safety-symbolic-params`: the parameters
  are replaced by opaque variables (outside of types and of the arguments of
  `is_arr_init`) through the safety instrumentation and its standard
  simplification, and by their values afterwards, so that the extraction is
  simplified as usual and still has the same shape at every value of the
  parameters (in the branches of conditionals that depend on parameters, the
  literal offsets of accesses to parameter-sized arrays stay opaque too, as
  their bound checks may hold at some values only). The orders and names are
  made size-independent as with `--no-safety-simplify`, which it excludes;
  `--safety-simplify-from=IDENT` applies to it as well.
