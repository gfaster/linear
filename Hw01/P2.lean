
import Mathlib.Tactic

namespace LH2 


inductive Expr where
  | Mul (l r : Expr)
  | Add (l r : Expr)
  | Num (n : Nat)


@[reducible]
def Expr.value : Expr → Prop
  | Num _ => True
  | _ => False

def Expr.value_of (e : Expr) (hv : e.value) : Nat := by
  cases e with
  | Num n => exact n
  | _ => contradiction

infixl:68 " ⊕ " => Expr.Add
infixl:69 " ⊗ " => Expr.Mul

@[reducible]
def num : Nat → Expr := Expr.Num

inductive Expr.Step : Expr → Expr → Prop where
  | MulL {l l' r : Expr} (hm : Expr.Step l l') 
    : Expr.Step (Expr.Mul l r) (Expr.Mul l' r)
  | MulR {l r r' : Expr} (hv : l.value) (hm : Expr.Step r r') 
    : Expr.Step (Expr.Mul l r) (Expr.Mul l' r)
  | MulVal {l r : Expr} (hvl : l.value) (hvr : r.value) 
    : Expr.Step (Expr.Mul l r) 
      (Expr.Num $ (l.value_of hvl) * (r.value_of hvr))
  | AddL {l l' r : Expr} (hm : Expr.Step l l') 
    : Expr.Step (Expr.Add l r) (Expr.Add l' r)
  | AddR {l r r' : Expr} (hv : l.value) (hm : Expr.Step r r') 
    : Expr.Step (Expr.Add l r) (Expr.Add l' r)
  | AddVal {l r : Expr} (hvl : l.value) (hvr : r.value) 
    : Expr.Step (Expr.Add l r) 
      (Expr.Num $ (l.value_of hvl) + (r.value_of hvr))

def Expr.Step.AddVal' (n1 n2 : Nat) 
  : Expr.Step (num n1 ⊕ num n2) (num $ n1 + n2) := by
    solve_by_elim


def Expr.Step.MulVal' (n1 n2 : Nat) 
  : Expr.Step (num n1 ⊗ num n2) (num $ n1 * n2) := by
    solve_by_elim

theorem Expr.Step.exists_step (e : Expr) 
  : (∃ e', Expr.Step e e') ∨ e.value := by
  induction e with
  | Mul l r IH1 IH2 => 
    constructor
    cases IH1 with
    | inl h => 
      obtain ⟨e', he'⟩ := h
      exists e' ⊗ r
      solve_by_elim
    | inr h => sorry


  | Add l r IH1 IH2 => sorry
  | Num n => right; trivial



example : (num 1 ⊕ num 2) = (num 3) := by
  sorry




end LH2
