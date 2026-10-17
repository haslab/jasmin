- `jasmin2ec --model safety` accepts `--no-safety-simplify`: the instrumented
  program is extracted without the final constant propagation and dead-code
  elimination, and the order of the initialisations of its init-tracking
  variables, the numbering of its variables and its auxiliary variables are
  made independent of array sizes, so that the shape of the extraction does not
  depend on the values of `param` declarations (needed for parametric safety
  proofs).
