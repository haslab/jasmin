(* -------------------------------------------------------------------- *)
exception InvalidRegSize of Word.wsize

(* -------------------------------------------------------------------- *)
val mangle : string -> string

(* -------------------------------------------------------------------- *)
val pp_instr : Format.formatter -> X86_sem.asm -> unit
val pp_prog  : 'info Conv.coq_tbl -> Format.formatter -> X86.xprog -> unit


