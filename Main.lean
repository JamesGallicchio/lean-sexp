import Sexp
import Sexp.Sexpable

open Sexp

inductive MyOption (α)
| none
| some (a : α)
deriving OfSexp

def main : IO Unit := do
  return ()