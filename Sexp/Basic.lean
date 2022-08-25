namespace Sexp

inductive Sexp
| atom (s : String)
| slist (ss : List Sexp)

namespace Sexp

def atomToString (s : String) : String :=
  if s.isEmpty || s.any ("\"() ".contains) then
    "\"" ++ String.replace s "\"" "\\\"" ++ "\""
  else
    s

theorem atomToString_nonempty (s : String)
  : (atomToString s).isEmpty = false
  := by
  simp [atomToString]
  split
  case inl h =>
    generalize String.replace s _ _ = s
    simp [HAppend.hAppend, Append.append, String.append]
    simp [String.isEmpty, String.endPos, String.utf8ByteSize, String.utf8ByteSize.go]
    generalize String.utf8ByteSize.go _ = rest
    simp [BEq.beq]
    apply decide_eq_false
    intro h
    cases h
  case inr h =>
    apply Decidable.byCases id
    intro h'
    have := eq_true_of_ne_false h'
    simp [this] at h

mutual
def toString : Sexp → String
| atom s => atomToString s
| slist ss => "(" ++ listToString ss ++ ")"

def listToString : List Sexp → String
| [] => ""
| [s] => toString s
| s :: ss => toString s ++ " " ++ listToString ss
end

instance : ToString Sexp where
  toString := toString

#eval (slist [
  (atom "hi"),
  (atom "bye"),
  (atom "no \"really"),
  (slist [(atom "what"), (atom "oh")])
])