
Record f_arity (S : Type) : Type :=
  { f_args : list S;
    f_out : S
  }.

Arguments f_args {_}.
Arguments f_out {_}.

Record r_arity (S : Type) : Type :=
  { r_args : list S }.

Arguments r_args {_}.

Record f_sig (S : Type) : Type :=
  { f_symbols : Type;
    f_arities : f_symbols -> f_arity S
  }.

Arguments f_symbols {_}.
Arguments f_arities {_} {_} _.

Record r_sig (S : Type) : Type :=
  { r_symbols : Type;
    r_arities : r_symbols -> r_arity S
  }.

Arguments r_symbols {_}.
Arguments r_arities {_} {_} _.

Record sig (S : Type) : Type :=
  { func : f_sig S;
    rel : r_sig S
  }.

Arguments func {_}.
Arguments rel {_}.
