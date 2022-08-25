import Lean

import Sexp.Basic


namespace Sexp

class ToSexp (α) where
  toSexp : α → Sexp

class OfSexp (α) where
  ofSexp : Sexp → α

open Lean
open Lean.Elab
open Lean.Elab.Deriving
open Command

def mkToSexpHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader `ToSexp 2 indVal

def mkToSexp (n : Name) : CommandElabM Bool := do
  return true

def mkOfSexp (n : Name) : CommandElabM Bool := do
  return true

def mkToSexpInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  IO.println "hi"
  if declNames.size != 1 then
    return true -- mutually inductive types are not supported yet
  else
    mkToSexp declNames[0]!

def mkOfSexpInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return true -- mutually inductive types are not supported yet
  else
    mkOfSexp declNames[0]!

builtin_initialize
  Lean.Elab.registerDerivingHandler `ToSexp mkToSexpInstanceHandler
  Lean.Elab.registerDerivingHandler `OfSexp mkOfSexpInstanceHandler
  Lean.registerTraceClass `Elab.Deriving.toSexp
  Lean.registerTraceClass `Elab.Deriving.ofSexp