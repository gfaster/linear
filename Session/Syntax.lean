import Session.Defs
import Lean

open Lean Elab Meta

declare_syntax_cat rast_bin_type
syntax "⊗"       : rast_bin_type
syntax "⊸"       : rast_bin_type



declare_syntax_cat rast_sum_type
syntax "⊕"       : rast_sum_type
syntax "&"       : rast_sum_type


declare_syntax_cat                                      rast_type
declare_syntax_cat                                    rast_type_var_bind
syntax ident ":" rast_type                          : rast_type_var_bind

syntax ident                                          : rast_type
syntax rast_sum_type "{" rast_type_var_bind,* "}"     : rast_type
syntax rast_type rast_bin_type rast_type              : rast_type
syntax "()"                                           : rast_type
syntax "(" rast_type ")"                              : rast_type



inductive RastBinType
  | Tensor | Lolli

inductive RastSumType
  | Add | With

inductive RastType
  | Var : Ident → RastType
  | Choice : RastSumType → Array (Ident × RastType) → RastType
  | Bin : RastType → RastBinType → RastType → RastType
  | One : RastType

declare_syntax_cat rast_proc_case
declare_syntax_cat rast_proc

syntax ident "=>" rast_proc : rast_proc_case

-- this is x.k
syntax ident "|" ident ";" rast_proc : rast_proc 
syntax ident "←" ident ident * ";" rast_proc : rast_proc
syntax ident "↔" ident : rast_proc
syntax "case" ident "(" rast_proc_case* ")" : rast_proc
syntax "close" ident : rast_proc
syntax "wait" ident ";" rast_proc : rast_proc
syntax "send" ident ident ";" rast_proc : rast_proc
syntax ident "←recv" ident ";" rast_proc : rast_proc

inductive RastExpr where
  | SendLabel (c k : Ident) : RastExpr → RastExpr
  | Spawn (x f : Ident) (arg : Array Ident) : RastExpr → RastExpr
  | Fwd (x p : Ident) : RastExpr
  | Case (c : Ident) : Array (Ident × RastExpr) → RastExpr
  | Close (c : Ident) : RastExpr
  | Wait (c : Ident) : RastExpr → RastExpr
  | Send (d c : Ident) : RastExpr → RastExpr
  | Recv (x c : Ident) : RastExpr → RastExpr



@[reducible]
def TyBind := Ident × RastType

structure RastTyDecl where
  name : Ident
  t : RastType

structure RastProcDecl where
  name : Ident
  args : Array TyBind
  ret : TyBind

structure RastProcImpl where
  offers : Ident
  name : Ident
  vars : Array Ident
  expr : RastExpr

inductive RastStmt where
  | TyDecl : RastTyDecl → RastStmt
  | ProcDecl : RastProcDecl → RastStmt
  | Proc : RastProcImpl → RastStmt

inductive RastDecl where
  | Ty : RastTyDecl → RastDecl
  | Proc : RastProcDecl → RastDecl


declare_syntax_cat rast_type_cx
syntax ("(" rast_type_var_bind ")")+ : rast_type_cx
syntax "·" : rast_type_cx

declare_syntax_cat rast_stmt
syntax "type " ident "=" rast_type: rast_stmt
syntax "decl " ident ":" rast_type_cx " ⊢ "
  "(" rast_type_var_bind ")" : rast_stmt
syntax "proc " ident "←" ident (ident)* " = " rast_proc : rast_stmt

declare_syntax_cat rast_prog
syntax (rast_stmt)* : rast_prog




structure RastModuleInner where
  decls : List RastDecl
  impls : List RastProcImpl

-- this needs to be a structure since afaict we get problems implementing
-- typeclasses otherwise
structure RastModule (α : Type) : Type where
  inner : MetaM (RastModuleInner × α)

section
variable (self : RastModule α)

end

instance : Monad RastModule where
  pure a := ⟨pure (⟨[], []⟩, a)⟩
  bind result next := 
    have inner := do
      let result ← result.inner
      let next ← (next result.snd).inner
      let decls := next.fst.decls ++ result.fst.decls
      let impls := next.fst.impls ++ result.fst.impls
      return (⟨decls, impls⟩, next.snd)
    ⟨inner⟩

-- instance RastModule.instLawfulMonad : LawfulMonad RastModule := by
  -- apply LawfulMonad.mk' <;> (introv; simp [RastModule.instMonad])

def runMeta (action : MetaM α) : RastModule α := 
  .mk (action >>= λ a => pure ⟨⟨[], []⟩, a⟩)

def addStmt : RastStmt → RastModule Unit
  | RastStmt.TyDecl dec => ⟨pure (⟨[.Ty dec], []⟩, Unit.unit)⟩
  | RastStmt.ProcDecl dec => ⟨pure (⟨[.Proc dec], []⟩, Unit.unit)⟩
  | RastStmt.Proc impl => ⟨pure (⟨[], [impl]⟩, Unit.unit)⟩

instance : MonadNameGenerator RastModule where
  getNGen := runMeta getNGen
  setNGen gen := runMeta (setNGen gen)




def elabRastSum : Syntax → MetaM RastSumType
  | `(rast_sum_type| ⊕) => return RastSumType.Add
  | `(rast_sum_type| &) => return RastSumType.With
  | _ => throwUnsupportedSyntax

def elabRastBin : Syntax → MetaM RastBinType
  | `(rast_bin_type| ⊗) => return RastBinType.Tensor
  | `(rast_bin_type| ⊸) => return RastBinType.Lolli
  | _ => throwUnsupportedSyntax

partial def elabRastType : Syntax → MetaM RastType
  | `(rast_type| $i:ident) => return RastType.Var i
  | `(rast_type| $l:rast_type $op:rast_bin_type $r:rast_type) => do
    let l ← elabRastType l
    let op ← elabRastBin op
    let r ← elabRastType r
    return RastType.Bin l op r
  | `(rast_type| $sum:rast_sum_type { $[$b:rast_type_var_bind],* }) => do
    let sum ← elabRastSum sum;
    let binds ← Array.mapM (λ 
      | `(rast_type_var_bind| $i:ident : $t:rast_type) => do
        let t ← elabRastType t
        return (i, t)
      | _ => throwUnsupportedSyntax
      ) b;
    return RastType.Choice sum binds
  | `(rast_type|()) => return RastType.One
  | `(rast_type|($r:rast_type)) => elabRastType r
  | _ => throwUnsupportedSyntax

def elabRastTypeBind : Syntax → MetaM TyBind
  | `(rast_type_var_bind| $bind:ident : $ty:rast_type) => do
    return (bind, ←elabRastType ty)
  | _ => throwUnsupportedSyntax

partial def elabRastExpr : Syntax → MetaM RastExpr 
  | `(rast_proc| $c:ident|$k:ident ; $rem:rast_proc) => do
    return RastExpr.SendLabel c k (←elabRastExpr rem)
  | `(rast_proc| $x:ident ← $f:ident $[$arg:ident]* ; $rem:rast_proc) => do
    return RastExpr.Spawn x f arg (←elabRastExpr rem)
  | `(rast_proc| $x:ident ↔ $p:ident) => do
    return RastExpr.Fwd x p
  | `(rast_proc| case $c:ident ( $[$branch:rast_proc_case]* )) => do
    let branch ← Array.mapM (λ 
      | `(rast_proc_case| $lab:ident => $body:rast_proc) => do
        return (lab, (←elabRastExpr body))
      | _ => throwUnsupportedSyntax
      ) branch
    return RastExpr.Case c branch
  | `(rast_proc| close $x:ident) => do
    return RastExpr.Close x
  | `(rast_proc| wait $x:ident ; $rem:rast_proc) => do
    return RastExpr.Wait x (← elabRastExpr rem)
  | `(rast_proc| send $d:ident $c:ident ; $rem:rast_proc) => do
    return RastExpr.Send d c (← elabRastExpr rem)
  | `(rast_proc| $x:ident ←recv $c:ident ; $rem:rast_proc) => do
    return RastExpr.Recv x c (← elabRastExpr rem)
  | _ => throwUnsupportedSyntax


def elabRastCx : Syntax → MetaM (Array TyBind)
  | `(rast_type_cx| ·) => pure #[]
  | `(rast_type_cx| $[($bind:rast_type_var_bind)]*) => do
    Array.mapM elabRastTypeBind bind
  | _ => throwUnsupportedSyntax

def elabRastStmt : Syntax → MetaM RastStmt
  | `(rast_stmt| type $name:ident = $ty:rast_type) => do
    return RastStmt.TyDecl ⟨name, (←elabRastType ty)⟩
  | `(rast_stmt| decl $name:ident : $cx:rast_type_cx 
      ⊢ ($offer:rast_type_var_bind) ) => do
    let cx ← elabRastCx cx
    let offer ← elabRastTypeBind offer
    return RastStmt.ProcDecl $ ⟨name, cx, offer⟩ 
  | `(rast_stmt| proc $name:ident ← 
      $f:ident $[$arg:ident]* = $p:rast_proc) => do
    let p ← elabRastExpr p
    return RastStmt.Proc $ ⟨name, f, arg, p⟩
  | _ => throwUnsupportedSyntax

def elabRastProgModule : Syntax → RastModule Unit
  | `(rast_prog| $[$stmts:rast_stmt]*) => do
    for stmt in stmts do
      let stmt ← runMeta $ elabRastStmt stmt
      addStmt stmt
  | _ => runMeta throwUnsupportedSyntax

def elabRastChoices : RastType → Command.CommandElabM Unit
  | .Choice _ labels => sorry
  | .Var _ => return Unit.unit
  | .Bin l _ r => do
    elabRastChoices l
    elabRastChoices r
  | .One => return Unit.unit


def elabRastDecl : RastDecl → Command.CommandElabM (List Ident)
  | .Ty ty => do
    let ⟨name, ty⟩ := ty
    sorry

  | .Proc pr => sorry


def elabRastModule (mod : RastModuleInner) : Command.CommandElabM Unit := do
  let ⟨decls, impls⟩ := mod



#check Unit




