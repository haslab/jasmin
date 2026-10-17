- `jasmin2ec --model safety` accepts `--no-safety-simplify`: the instrumented
  program is extracted without the final constant propagation and dead-code
  elimination, and the initialisations of its init-tracking variables are
  emitted in an order that does not depend on array sizes, so that the shape of
  the extraction does not depend on the values of `param` declarations (needed
  for parametric safety proofs).
