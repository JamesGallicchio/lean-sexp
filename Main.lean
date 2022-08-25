import Sexp

open Sexp

inductive MyOption (α)
| none
| some (a : α)
deriving ToSexp

def main : IO Unit := do
  return ()