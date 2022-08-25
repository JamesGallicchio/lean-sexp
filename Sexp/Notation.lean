import Sexp.Basic

namespace Sexp.Notation

declare_syntax_cat sexp

syntax ident : sexp
syntax str : sexp
syntax "(" sexp* ")" : sexp

syntax "`[Sexp| " sexp "]" : term
syntax "`[Sexps| " sexp* "]" : term

scoped macro_rules
  | `(`[Sexp| $s:ident])    => `(Sexp.atom $(Lean.quote s.getId.toString))
  | `(`[Sexp| $s:str])      => `(Sexp.atom $s)
  | `(`[Sexp| ($ss:sexp*)]) => `(Sexp.slist `[Sexps| $ss*])
  | `(`[Sexps| ])                   => `([])
  | `(`[Sexps| $s:sexp])            => `([`[Sexp| $s]])
  | `(`[Sexps| $s:sexp $ss:sexp* ]) => `((`[Sexp| $s]) :: (`[Sexps| $ss*]))

#eval `[Sexp| (hi ((bye) "tri " ( ))) ]

end Sexp.Notation
