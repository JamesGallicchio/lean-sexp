import Lean

import Sexp.Basic


namespace Sexp

class ToSexp (α) where
  toSexp : α → Sexp

class OfSexp (α) where
  ofSexp : Sexp → Option α

namespace Sexpable

open Lean
open Lean.Elab
open Lean.Elab.Deriving
open Lean.Elab.Command
open Lean.Parser.Term
open Lean.Meta

def mkToSexpAlts (indVal : InductiveVal)
    (rhs : ConstructorVal → Array (Ident × Expr) → Option (Array Name) → TermElabM Term)
  : TermElabM (Array (TSyntax ``matchAlt)) := do
  indVal.ctors.toArray.mapM fun ctor => do
    let ctorInfo ← getConstInfoCtor ctor
    forallTelescopeReducing ctorInfo.type fun xs _ => do
      let mut patterns := #[]
      -- add `_` pattern for indices
      for _ in [:indVal.numIndices] do
        patterns := patterns.push (← `(_))
      let mut ctorArgs := #[]
      -- add `_` for inductive parameters, they are inaccessible
      for _ in [:indVal.numParams] do
        ctorArgs := ctorArgs.push (← `(_))
      -- bound constructor arguments and their types
      let mut binders := #[]
      let mut userNames := #[]
      for i in [:ctorInfo.numFields] do
        let x := xs[indVal.numParams + i]!
        let localDecl ← x.fvarId!.getDecl
        if !localDecl.userName.hasMacroScopes then
          userNames := userNames.push localDecl.userName
        let a := mkIdent (← mkFreshUserName `a)
        binders := binders.push (a, localDecl.type)
        ctorArgs := ctorArgs.push a
      patterns := patterns.push (← `(@$(mkIdent ctorInfo.name):ident $ctorArgs:term*))
      let rhs ← rhs ctorInfo binders (if userNames.size == binders.size then some userNames else none)
      `(matchAltExpr| | $[$patterns:term],* => $rhs:term)


def mkToSexp (n : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct n
  let cmds ← liftTermElabM do
    let ctx ← mkContext "toSexp" n
    let toSexpFuncId := mkIdent ctx.auxFunNames[0]!
    -- Return syntax to sexpify `id`, either via `ToSexp` or recursively
    -- if `id`'s type is the type we're deriving for.
    let mkToSexp (id : Ident) (type : Expr) : TermElabM Term := do
      if type.isAppOf indVal.name then `($toSexpFuncId:ident $id:ident)
      else ``(ToSexp.toSexp $id:ident)
    let header ← mkHeader ``ToSexp 1 ctx.typeInfos[0]!
    let discrs ← mkDiscrs header indVal
    let alts ← mkToSexpAlts indVal fun ctor args userNames => do
      match args, userNames with
      -- | #[], _ => ``(ToSexp.toSexp $(quote ctor.name.getString!))
      -- | #[(x, t)], none => ``(mkObj [($(quote ctor.name.getString!), $(← mkToSexp x t))])
      | xs, _ =>
        let xs ← xs.mapM fun (x, t) => mkToSexp x t
        ``(Sexp.slist (Sexp.atom $(quote ctor.name.getString!) :: $(quote xs.toList)))
      -- | xs, some userNames =>
      --   let xs ← xs.mapIdxM fun idx (x, t) => do
      --     `(($(quote userNames[idx]!.getString!), $(← mkToSexp x t)))
      --   ``(mkObj [($(quote ctor.name.getString!), mkObj [$[$xs:term],*])])
    let auxTerm ← `(match $[$discrs],* with $alts:matchAlt*)
    let auxCmd ←
      if ctx.usePartial then
        let letDecls ← mkLocalInstanceLetDecls ctx ``ToSexp header.argNames
        let auxTerm ← mkLet letDecls auxTerm
        `(private partial def $toSexpFuncId:ident $header.binders:bracketedBinder* : Sexp := $auxTerm)
      else
        `(private def $toSexpFuncId:ident $header.binders:bracketedBinder* : Sexp := $auxTerm)
    return #[auxCmd] ++ (← mkInstanceCmds ctx ``ToSexp #[n])
  cmds.forM elabCommand
  return true

def mkOfSexp (n : Name) : CommandElabM Bool := do
  return true

def mkToSexpInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  else
    mkToSexp declNames[0]!

def mkOfSexpInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  else
    mkOfSexp declNames[0]!

builtin_initialize
  Lean.Elab.registerDerivingHandler ``ToSexp mkToSexpInstanceHandler
  Lean.Elab.registerDerivingHandler ``OfSexp mkOfSexpInstanceHandler



instance : ToSexp String where
  toSexp s := Sexp.atom s

instance : OfSexp String where
  ofSexp s := s.atom?

instance : ToSexp Nat where
  toSexp n := Sexp.atom n.repr

instance : OfSexp Nat where
  ofSexp s := s.atom?.bind String.toNat?

#eval mkToSexpInstanceHandler #[``List]
#eval mkToSexpInstanceHandler #[``Option]

#eval ToSexp.toSexp [some "hi", none]

deriving instance ToSexp for List
deriving instance OfSexp for List