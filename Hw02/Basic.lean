import Mathlib.Data.Finmap
import Mathlib.Tactic

namespace SystemT



@[reducible]
def Var := Nat
  deriving DecidableEq



inductive Ty where
  | Func : Ty → Ty → Ty
  | Nat : Ty
  deriving DecidableEq

inductive Expr where
  | Lam (ty : Ty) (body : Expr)
  | App (func arg : Expr)
  | Zero
  | Succ (e : Expr)
  | NatRec (v e0: Expr) (e1 : Expr)
  | Var (x : Var)

def Expr.is_lambda : Expr → Prop 
  | Lam _ _ => True
  | _ => False

inductive Expr.equiv_mod_vars : Expr → Expr → Prop where
  | Lam (h : e1.equiv_mod_vars e2) 
    : Expr.equiv_mod_vars (Expr.Lam α e1) (Expr.Lam α e2)
  | App (hf : f1.equiv_mod_vars f2) (ha : a1.equiv_mod_vars a2)
    : Expr.equiv_mod_vars (Expr.App f1 a1) (Expr.App f2 a2)
  | Zero : Expr.equiv_mod_vars Expr.Zero Expr.Zero
  | Succ (h : e1.equiv_mod_vars e2) 
    : Expr.equiv_mod_vars (Expr.Succ e1) (Expr.Succ e2)
  | NatRec 
    (hv : v1.equiv_mod_vars v2) 
    (hz : z1.equiv_mod_vars z2) 
    (he : e1.equiv_mod_vars e2)
    : Expr.equiv_mod_vars (Expr.NatRec v1 z1 e1) (Expr.NatRec v2 z2 e2)
  | Var : Expr.equiv_mod_vars (Expr.Var v1) (Expr.Var v2)

inductive Expr.equiv_mod_free_vars : Expr → Expr → Nat → Prop where
  | Lam (h : e1.equiv_mod_free_vars e2 (d + 1)) 
    : Expr.equiv_mod_free_vars (Expr.Lam α e1) (Expr.Lam α e2) d
  | App (hf : f1.equiv_mod_free_vars f2 d) (ha : a1.equiv_mod_free_vars a2 d)
    : Expr.equiv_mod_free_vars (Expr.App f1 a1) (Expr.App f2 a2) d
  | Zero : Expr.equiv_mod_free_vars Expr.Zero Expr.Zero d
  | Succ (h : e1.equiv_mod_free_vars e2 d) 
    : Expr.equiv_mod_free_vars (Expr.Succ e1) (Expr.Succ e2) d
  | NatRec 
    (hv : v1.equiv_mod_free_vars v2 d) 
    (hz : z1.equiv_mod_free_vars z2 d) 
    (he : e1.equiv_mod_free_vars e2 (d + 2))
    : Expr.equiv_mod_free_vars (Expr.NatRec v1 z1 e1) (Expr.NatRec v2 z2 e2) d
  | Var (h : (v1 > d ∧ v2 > d) ∨ v1 = v2)
    : Expr.equiv_mod_free_vars (Expr.Var v1) (Expr.Var v2) d

theorem Expr.equiv_mod_free_vars.of_depth_gt
  (h : Expr.equiv_mod_free_vars e1 e2 n) 
  : ∀ n' < n, e1.equiv_mod_free_vars e2 n' := by
    intros n' hgt
    induction h generalizing n' with
    | Zero => constructor
    | Var h1 => 
      constructor
      cases h1 with
      | inl h1 => 
        left
        simp only [gt_iff_lt] at h1 ⊢
        obtain ⟨h1, h2⟩ := h1
        constructor
        · exact Nat.lt_trans hgt h1
        · exact Nat.lt_trans hgt h2
      | inr h1 =>
        right
        trivial
    | _ => all_goals
      constructor <;> (apply_assumption ; simp [hgt])

theorem Expr.equiv_mod_free_vars.zero_eq 
  : (Expr.Zero.equiv_mod_free_vars e n) → e = Expr.Zero := by
    intro h
    cases h
    rfl


inductive Expr.var_appears : Expr → SystemT.Var → Prop where
  | Lam (h : e.var_appears (d + 1)) 
    : Expr.var_appears (Expr.Lam α e)  d
  | AppF (h : f.var_appears d)
    : Expr.var_appears (Expr.App f a) d
  | AppA (h : a.var_appears d)
    : Expr.var_appears (Expr.App f a) d
  | Succ (h : e.var_appears d) 
    : Expr.var_appears (Expr.Succ e) d
  | NatRecE (h : e.var_appears d) 
    : Expr.var_appears (Expr.NatRec e e0 e1) d
  | NatRecE0 (h : e0.var_appears d) 
    : Expr.var_appears (Expr.NatRec e e0 e1) d
  | NatRecE1 (h : e1.var_appears (d + 2)) 
    : Expr.var_appears (Expr.NatRec e e0 e1) d
  | Var (h : d = v) : Expr.var_appears (Expr.Var v) d


-- inductive Expr.equiv_over_vars : Expr → Expr → Nat → Prop where
--   | Lam (h : e1.equiv_mod_free_vars e2 (d + 1)) 
--     : Expr.equiv_mod_free_vars (Expr.Lam α e1) (Expr.Lam α e2) d
--   | App (hf : f1.equiv_mod_free_vars f2 d) (ha : a1.equiv_mod_free_vars a2 d)
--     : Expr.equiv_mod_free_vars (Expr.App f1 a1) (Expr.App f2 a2) d
--   | Zero : Expr.equiv_mod_free_vars Expr.Zero Expr.Zero d
--   | Succ (h : e1.equiv_mod_free_vars e2 d) 
--     : Expr.equiv_mod_free_vars (Expr.Succ e1) (Expr.Succ e2) d
--   | NatRec 
--     (hv : v1.equiv_mod_free_vars v2 d) 
--     (hz : z1.equiv_mod_free_vars z2 d) 
--     (he : e1.equiv_mod_free_vars e2 (d + 2))
--     : Expr.equiv_mod_free_vars (Expr.NatRec v1 z1 e1) (Expr.NatRec v2 z2 e2) d
--   | Var (h1 : (v1 > d ∧ v2 > d) ∨ v1 = v2)
--     : Expr.equiv_mod_free_vars (Expr.Var v1) (Expr.Var v2) d

theorem Expr.is_lambda_iff (e : Expr) 
  : (∃ α e', e = Expr.Lam α e') ↔ e.is_lambda := by
  -- dsimp [Expr.is_lambda]
  constructor
  · intro ⟨τ, e', heq⟩
    subst heq
    trivial
  · intro h
    simp [Expr.is_lambda] at h
    cases e <;> (reduce at h; try contradiction)
    case mpr.Lam ty body => exists ty, body



def Expr.of_lambda (e : Expr) (h : e.is_lambda) :=
  match e with
  | .Lam α e => Expr.Lam α e
  | .App _ _ | .Zero | .Succ _ | .NatRec _ _ _ | Var _
  => by
    absurd h
    dsimp [Expr.is_lambda]
    trivial

def Expr.of_lambda' (e : Expr) (h : e.is_lambda) :=
  match e with
  | .Lam α e => (α, e)
  | .App _ _ | .Zero | .Succ _ | .NatRec _ _ _ | Var _
  => by
    absurd h
    dsimp [Expr.is_lambda]
    trivial


def Expr.bind_depth : Expr → Nat
  | Lam  _ body => 1 + body.bind_depth
  | App func arg => func.bind_depth.max arg.bind_depth
  | Zero => 1
  | Succ e => e.bind_depth
  | NatRec v e0 e1 => v.bind_depth.max $
      e0.bind_depth.max $
      (2 + e1.bind_depth)
  | Var _ => 1



def Expr.of_nat : Nat → Expr
  | .succ n => Expr.Succ $ Expr.of_nat n
  | .zero => Expr.Zero

abbrev Cx := List Ty

def DeBruijin (α : Type) : Type := Nat → α

@[reducible]
def DeBruijin.root (action : DeBruijin α) : α := action 0

-- https://en.wikipedia.org/wiki/De_Bruijn_index
instance : Monad DeBruijin where
  pure x := fun _ => x
  bind res next := fun cx => next (res cx) cx

instance : LawfulMonad DeBruijin := by 
  apply LawfulMonad.mk' DeBruijin
  · solve_by_elim
  · solve_by_elim
  · introv
    solve_by_elim

@[reducible]
def in_bind  (action : DeBruijin α)  : DeBruijin α :=
  fun depth => action depth.succ

@[reducible]
def in_bind2  (action : DeBruijin α)  : DeBruijin α :=
  fun depth => action depth.succ.succ

@[reducible]
def curr_depth : DeBruijin Nat := fun depth => depth

def var_eq (v : Var) : DeBruijin (Var → Prop) := fun depth =>
  fun v' => Nat.add v depth = v'



inductive Expr.lawful_depth : Expr → DeBruijin Prop where
  | Lam (h : lawful_depth e (d + 1)) 
    : lawful_depth (Expr.Lam α e) d
  | App (hf : lawful_depth f d) (ha : lawful_depth a d)
    : lawful_depth (Expr.App f a) d
  | Zero : lawful_depth Expr.Zero d
  | Succ (h : lawful_depth e d) : lawful_depth (Expr.Succ e) d
  | NatRec 
    (he : lawful_depth e d)
    (he0 : lawful_depth e0 d)
    (he1 : lawful_depth e1 (d + 2))
    : lawful_depth (Expr.NatRec e e0 e1) d
  | Var (h : v < d) : lawful_depth (Expr.Var v) d

theorem Expr.lawful_depth.of_lt (hld : Expr.lawful_depth e d) (h : d < d') 
  : e.lawful_depth d' := by
  induction hld generalizing d' with
  | Lam => 
    constructor
    apply_assumption
    simpa
  | NatRec =>
    constructor
    · solve_by_elim
    · solve_by_elim
    apply_assumption
    simpa
  | Var hv=> 
    constructor
    exact Nat.lt_trans hv h
  | _ => solve_by_elim
  

-- structure ExprDepth (depth : Nat) where
--   expr : Expr
--   depth_lawful : expr.lawful_depth depth

-- inductive Expr.equiv_mod_free_vars_lawful : Expr → Expr → Nat → Prop where
--   | Lam 
--     (h : e1.equiv_mod_free_vars_lawful e2 (d + 1)) 
--     : Expr.equiv_mod_free_vars_lawful (Expr.Lam α e1) (Expr.Lam α e2) d
--   | App 
--     (hf : f1.equiv_mod_free_vars_lawful f2 d)
--     (ha : a1.equiv_mod_free_vars a2 d)
--     : Expr.equiv_mod_free_vars_lawful (Expr.App f1 a1) (Expr.App f2 a2) d
--   | Zero : Expr.equiv_mod_free_vars_lawful Expr.Zero Expr.Zero d
--   | Succ 
--     (h : e1.equiv_mod_free_vars_lawful e2 d) 
--     : Expr.equiv_mod_free_vars_lawful (Expr.Succ e1) (Expr.Succ e2) d
--   | NatRec 
--     (hv : v1.equiv_mod_free_vars_lawful v2 d) 
--     (hz : z1.equiv_mod_free_vars_lawful z2 d) 
--     (he : e1.equiv_mod_free_vars_lawful e2 (d + 2))
--     : Expr.equiv_mod_free_vars_lawful 
--       (Expr.NatRec v1 z1 e1) 
--       (Expr.NatRec v2 z2 e2) d
--   | Var (h1 : (v1 > d ∧ v2 > d) ∨ v1 = v2)
--     : Expr.equiv_mod_free_vars_lawful (Expr.Var v1) (Expr.Var v2) d


-- instance : Insert (Var × Ty) Cx where
--   insert v := Finmap.insert v.fst v.snd

-- instance : Membership (Var × Ty) Cx  where
--   mem b Γ := Γ.foldl (fun acc k v => acc ∨ ((k, v) = b)) (by
--     introv
--     obtain ⟨b0, b1⟩ := b
--     beta_reduce
--     simp
--     constructor
--     · intro h
--       casesm* _ ∨ _, _ ∧ _
--       · solve_by_elim
--       · subst_vars; simp
--       · subst_vars; simp
--     · intro h
--       casesm* _ ∨ _, _ ∧ _
--       · solve_by_elim
--       · subst_vars; simp
--       · subst_vars; simp
--   ) False


inductive Typed : Cx → Expr → Ty → Prop where
  | Lam (h : Typed (α :: Γ) body τ) 
    : Typed Γ (Expr.Lam α body) (Ty.Func α τ)
  | App (hf : Typed Γ e1 (Ty.Func α τ)) (ha : Typed Γ e2 α)
    : Typed Γ (Expr.App e1 e2) τ
  | Var (hx : x < Γ.length)
    : Typed Γ (Expr.Var x) (Γ[x])
  | Zero 
    : Typed Γ (Expr.Zero) Ty.Nat
  | Succ (h : Typed Γ e Ty.Nat)
    : Typed Γ (Expr.Succ e) Ty.Nat
  | Rec (hr : Typed Γ e Ty.Nat)
        (h0 : Typed Γ e0 τ)
        (h1 : Typed (τ :: Ty.Nat :: Γ) e1 τ)
    : Typed Γ (Expr.NatRec e e0 e1) τ



-- def Typed.cx {Γ : Cx} (_ : Typed Γ e t) : Cx := Γ
-- def Typed.expr {Γ : Cx} (_ : Typed Γ e t) : Expr := e
-- def Typed.ty {Γ : Cx} (_ : Typed Γ e t) : Ty := t
--
-- def Ty.bool : Ty := Ty.Nat
-- def Expr.true : Expr := Expr.of_nat 1
-- def Expr.true.ty : Typed Γ Expr.true Ty.bool := by solve_by_elim
--
-- def Expr.false : Expr := Expr.of_nat 0
-- def Expr.false.ty : Typed Γ Expr.false Ty.bool := by solve_by_elim

def Expr.value : Expr → Prop 
  | .Lam _ _ => True
  | .Zero => True
  | .Succ _ => True
  | _ => False


theorem var_appears_bound_of_typed (h : Typed Γ e τ) 
  : e.var_appears x → x < Γ.length := by
  intro ha
  induction h generalizing x with
  | Lam =>
    cases ha
    rename ∀ _, _ => IH
    rename Expr.var_appears _ _ => h
    have := IH h
    simpa
  | App => cases ha <;> solve_by_elim
  | Var => cases ha; subst_vars; assumption
  | Zero => contradiction
  | Succ => cases ha; solve_by_elim
  | Rec _ _ _ IH IH0 IH1 =>
    cases ha
    · solve_by_elim
    · solve_by_elim
    · rename Expr.var_appears _ _ => h
      have := IH1 h
      simpa






def Expr.map_var (f : SystemT.Var → DeBruijin Expr) : Expr → DeBruijin Expr
  | .Lam α e => do
    let e' ← in_bind (e.map_var f)
    return Expr.Lam α e'
  | .App fn a => do
    let fn' ← fn.map_var f
    let a' ← a.map_var f
    return .App fn' a'
  | .Zero => pure .Zero
  | .Succ e => .Succ <$> e.map_var f
  | .NatRec v e0 e1 => do
    let v' ← v.map_var f
    let e0' ← e0.map_var f
    let e1' ← in_bind2 (e1.map_var f)
    return .NatRec v' e0' e1'
  | .Var x => f x


def map_free (f : Nat → Nat) : Expr → Expr :=
  fun e =>
    DeBruijin.root $ e.map_var $ (fun (v : Nat) => do
      return .Var $ if (←curr_depth) < v then f v else v
    )

def dec_free : Expr → Expr := map_free Nat.pred
def inc_free (amt : Nat) : Expr → Expr := map_free (Nat.add amt)

def map_free' (f : Nat → Nat) (depth : Nat) : Expr → Expr
  | .Lam ty e => .Lam ty (map_free' f depth.succ e)
  | .App func arg => .App (map_free' f depth func) (map_free' f depth arg)
  | .Zero => .Zero
  | .Succ e => .Succ $ map_free' f depth e
  | .NatRec v e0 e1 => .NatRec 
    (map_free' f depth v) 
    (map_free' f depth e0) 
    (map_free' f (depth + 2) e1)
  | .Var v => .Var $ if depth < v then f v else v

def inc_free' (amt : Nat) : Expr → Expr := 
  map_free' (Nat.add amt) 0

def dec_free' : Expr → Expr := 
  map_free' Nat.pred 0

theorem map_free_eq {f : Nat → Nat} : map_free f = map_free' f 0 := by
  apply_ext_theorem; intro e
  unfold map_free DeBruijin.root
  unfold_projs
  simp
  generalize 0 = d;
  induction e generalizing d
  all_goals {
    first | trivial | 
    unfold Expr.map_var map_free'
    unfold_projs
    simp
    solve_by_elim
  }


@[simp]
theorem map_free_lam {d : Nat} 
  : map_free' f d (Expr.Lam α e) = Expr.Lam α (map_free' f (d + 1) e) := by
  conv => lhs; unfold map_free'

@[simp]
theorem map_free_app {d : Nat} 
  : map_free' f d (Expr.App e1 e2) 
  = Expr.App (map_free' f d e1) (map_free' f d e2) := by
  conv => lhs; unfold map_free'

@[simp]
theorem map_free_succ {d : Nat} 
  : map_free' f d (Expr.Succ e) = Expr.Succ (map_free' f d e) := by
  conv => lhs; unfold map_free'

@[simp]
theorem map_free_zero {d : Nat} 
  : map_free' f d Expr.Zero = Expr.Zero  := by trivial

@[simp]
theorem map_free_nat_rec {d : Nat} 
  : map_free' f d (Expr.NatRec e e0 e1) 
  = Expr.NatRec 
    (map_free' f d e)
    (map_free' f d e0)
    (map_free' f (d + 2) e1)
    := by
  conv => lhs; unfold map_free'




theorem is_lambda_of_dec_free {e : Expr} (h : e.is_lambda) :
  Expr.is_lambda (dec_free e) := by
    unfold dec_free
    apply (Expr.is_lambda_iff _).mpr at h
    obtain ⟨τ, body, h⟩ := h
    subst h
    solve_by_elim


theorem map_free_equiv_mod_free (hinc : ∀ n, n ≤ f n)
  : Expr.equiv_mod_free_vars e (map_free' f depth e) depth := by
  induction e generalizing depth
  all_goals try solve_by_elim
  case Var v =>
  constructor
  have := hinc v
  split_ifs
  · left
    have : depth < f v :=
      by refine Nat.lt_of_lt_of_le ?_ (hinc v); assumption
    trivial
  · right; rfl

def map_free_flat (f : Nat → Nat) (depth : Nat) : Expr → Expr
  | .Lam ty e => .Lam ty (map_free_flat f depth.succ e)
  | .App func arg => .App 
    (map_free_flat f depth func) 
    (map_free_flat f depth arg)
  | .Zero => .Zero
  | .Succ e => .Succ $ map_free_flat f depth e
  | .NatRec v e0 e1 => .NatRec 
    (map_free_flat f depth v) 
    (map_free_flat f depth e0) 
    (map_free_flat f (depth + 2) e1)
  | .Var v => .Var $ if v < depth then v else f (v - depth) + depth

inductive all_of_free (p : Var → Prop) : Expr → DeBruijin Prop where
  | Lam (h : in_bind ( all_of_free p e) d) 
    : all_of_free p (Expr.Lam α e) d
  | App (hf : all_of_free p f d) (ha : all_of_free p a d)
    : all_of_free p (Expr.App f a) d
  | Zero 
    : all_of_free p Expr.Zero d
  | Succ (h : all_of_free p e d)
    : all_of_free p (Expr.Succ e) d
  | NatRec 
    (he : all_of_free p e d)
    (he0 : all_of_free p e0 d)
    (he1 : in_bind2 (all_of_free p e1) d)
    : all_of_free p (Expr.NatRec e e0 e1) d
  | Var {v : Var} (h : d < v → p (v - d)) 
    : all_of_free p (Expr.Var v) d

-- def all_of_free (p : (Var → DeBruijin Prop)) (e : Expr) : Prop :=
--   map_free

@[reducible]
def add_nat_cancel {n1 n2 : ℕ} (hdlt : n2 ≤ n1) : Fin (n1 - n2) → Fin n1 :=
  fun n => by
    have x := n.addNat n2
    rw [Nat.sub_add_cancel hdlt] at x
    exact x

lemma cons_len_le (h : a ≤ b.length) : ∀ α, a + 1 ≤ (α :: b).length := by
  intro α
  rw [List.length_cons]
  exact Nat.add_le_add_right h 1

@[reducible]
def adjust_map (map : Fin (n1 - n2) → Fin n3) (amt : ℕ)
  : Fin (n1 + amt - (n2 + amt)) → Fin (amt + n3) := by
  intro x
  conv at x =>
    arg 1
    rw [Nat.add_sub_add_right]
  exact (map x).natAdd amt


def adjust_map2 {l li : Cx} (map : Fin (li.length - n2) → Fin l.length)
  : Fin ((α :: li).length - (n2 + 1)) → Fin (α :: l).length := by
  intro x
  rw [List.length_cons] at x
  conv at x =>
    arg 1
    rw [Nat.add_sub_add_right]
  rw [List.length_cons, add_comm]
  exact (map x).natAdd 1

-- def adjust_map2 {l li : Cx} (map : (n : ℕ) → (nli.length - n2) → Fin l.length)
--   : Fin ((α :: li).length - (n2 + 1)) → Fin (α :: l).length := by
--   intro x
--   rw [List.length_cons] at x
--   conv at x =>
--     arg 1
--     rw [Nat.add_sub_add_right]
--   rw [List.length_cons, add_comm]
--   exact (map x).natAdd 1



-- example 
--   {Γ Δ : Cx}
--   (ht : Typed (Γ ++ Δ) e τ)
--   (hld : e'.lawful_depth (Γ ++ Δ).length)
--   (heq : e.equiv_mod_free_vars e' Γ.length)
--   ⦃Δ' : Cx⦄
--   (map : Fin Δ.length → Fin Δ'.length)
--   (hmap : ∀ (i : Fin Δ.length), 
--     Δ.get i = Δ'.get (map i))
--   : Typed (Γ ++ Δ') e' τ := by
--   generalize hcat : Γ ++ Δ = Γ' at *
--   induction ht generalizing e' Γ with
--   | Lam e IH => 
--     cases heq with | Lam heq =>
--     cases hld
--     constructor
--     rw [← @List.cons_append]
--     apply_assumption <;> simpa
--   | App hf ha IH1 IH2=> 
--     cases heq with | App heq1 heq2 =>
--     cases hld
--     skip
--     refine Typed.App (IH1 heq1 hcat ?_) (IH2 heq2 hcat ?_)
--     all_goals assumption
--   | Zero => 
--     cases heq
--     constructor
--   | Succ e IH =>
--     cases heq
--     cases hld
--     solve_by_elim
--   | Rec hte ht0 ht1 IHe IH0 IH1 => 
--     cases heq with | NatRec heqe heq0 heq1 =>
--     cases hld
--     constructor
--     · solve_by_elim
--     · solve_by_elim
--     repeat1 rw [← List.cons_append]
--     apply IH1
--     · solve_by_elim
--     · simpa
--     · simpa
--   | Var =>
--     cases heq with | Var heq =>
--     cases hld with | Var hld =>
--     rename Var => v2
--     subst hcat
--     rename Fin ((Γ ++ Δ).length) => x
--     cases heq with
--     | inl hgt => 
--       simp only [gt_iff_lt] at hgt
--       obtain ⟨hgt1, hgt2⟩ := hgt
--       generalize ha : (Γ ++ Δ).get x = α at *
--       obtain ⟨i, hi⟩ := x
--       simp at hgt1
--       have hi' := hi
--       simp at hi'
--       rw [add_comm] at hi'
--       -- apply Nat.sub_lt_right_of_lt_add
--       replace hi' := by 
--         exact Nat.sub_lt_right_of_lt_add (le_of_lt hgt1) hi'
--       sorry
--     | inr heq => sorry

@[reducible]
def fin_fun_to_nat (f : Fin n1 → Fin n2) : ℕ → ℕ := fun x =>
  if h : x < n1 then f ⟨x, h⟩ else 0

@[reducible]
def length_append' {Δ : Cx} (x : Fin Δ.length) (Γ : Cx) 
  : Fin (Δ ++ Γ).length := by
  obtain ⟨x, hx⟩ := x
  constructor
  swap
  · exact x + Γ.length
  rw [List.length_append]
  simpa


theorem map_free_flat_eq 
  {Γ Δ : Cx}
  (ht : Typed (Γ ++ Δ) e τ)
  (map : Nat → Nat)
  (hmapr : ∀ n < Δ.length, map n < Δ'.length)
  (hmap : ∀ v, {h1 : v < Δ.length} → {h2 : map v < Δ'.length} → Δ'[map v] = Δ[v])
  : Typed (Γ ++ Δ') (map_free_flat map Γ.length e) τ := by
  generalize hcat : Γ ++ Δ = Γ' at *
  induction ht generalizing Γ with
  | Lam _ IH => 
    constructor
    rw [← @List.cons_append]
    apply_assumption
    simpa
  | App _ _ IH1 IH2=> 
    constructor
    · solve_by_elim
    apply_assumption
    assumption
  | Zero => constructor
  | Succ _ IH => solve_by_elim
  | Rec _ _ _ IHe IH0 IH1 => 
    constructor
    · solve_by_elim
    · solve_by_elim
    repeat1 rw [← List.cons_append]
    apply IH1
    rw [←hcat]
    repeat1 rw [← List.cons_append]
  | Var hv =>
    rename Var => v
    subst hcat
    simp only [map_free_flat]
    generalize hv' : (if v < List.length Γ then v else map (v - List.length Γ) + List.length Γ) = v' at *
    have _ : v' < (Γ ++ Δ').length := by 
      rw [List.length_append]
      subst hv'
      split_ifs with hlt
      · exact Nat.lt_add_right (List.length Δ') hlt
      · nth_rewrite 2 [add_comm]
        rewrite [Nat.add_lt_add_iff_right]
        apply hmapr 
        simp at hv hlt
        exact Nat.sub_lt_left_of_lt_add hlt hv
    have : (Γ ++ Δ)[v] = (Γ ++ Δ')[v'] := ?_
    · rw [this]; constructor
    subst v'
    split_ifs with hlt
    · 
      simp at hlt
      simp [List.getElem_append_left _ _ hlt]
    · 
      simp at hlt hv
      -- simp [Nat.sub_lt_left_of_lt_add hlt hv]
      rw [List.getElem_append_right' hlt _]
      rw [List.getElem_append_right Γ Δ' ?_]
      simp [List.getElem_append_right]
      apply Eq.symm
      · apply hmap
      · simp
      simp
      apply hmapr
      exact Nat.sub_lt_left_of_lt_add hlt hv
      -- oh my god this was hell

def inc_free'' (amt : Nat) : Expr → Expr := 
  map_free_flat (Nat.add amt) 0

lemma inc_free_of_inc_free 
  (x y : ℕ) : inc_free'' x (inc_free'' y e) = inc_free'' (x + y) e := by
  unfold inc_free''
  generalize 0 = d
  induction e generalizing d with
  | Zero => constructor
  | Var v => 
    dsimp [map_free_flat]
    split_ifs with h1 h2
    · rfl
    · simp_arith at h1 h2
    · simp
      group
  | _ => 
    unfold map_free_flat
    reduce
    simp
    solve_by_elim

@[simp]
lemma inc_free_of_zero : inc_free'' 0 e = e := by
  unfold inc_free''
  have : Nat.add 0 = id := by funext; simp
  rw [this]; clear this
  generalize 0 = d
  induction e generalizing d with
  | Lam =>
    dsimp [map_free_flat]
    solve_by_elim
  | App f a hf ha =>
    dsimp [map_free_flat]
    rw [hf d, ha d]
  | Zero => rfl
  | Succ e IH =>
    dsimp [map_free_flat]
    rw [IH d]
  | NatRec e e0 e1 IHe IH0 IH1 =>
    simp [map_free_flat]
    solve_by_elim
  | Var v =>
    dsimp [map_free_flat]
    split_ifs with h
    · rfl
    · simp at h ⊢
      exact Nat.sub_add_cancel h






def Expr.beta_subst (body : Expr) (e : Expr)
  : Expr :=
    let map := map_var (fun v => do
      let depth ← curr_depth
      if depth = v then
        return inc_free'' depth e
      else if depth < v then
        -- v is free, so decrement it - helps avoid redundant work
        return .Var (v - 1)
      else
        return .Var v
    )
    (in_bind $ map body).root

-- Inefficient implementation of [x := body]e
--
-- I'm hoping it will be easier to do proofs with
def Expr.subst' (x : SystemT.Var) (body : Expr) : Expr → Expr 
  | Lam ty e => .Lam ty (Expr.subst' x.succ (inc_free'' 1 body) e)
  | App func arg => .App (Expr.subst' x body func) (Expr.subst' x body arg)
  | Zero => .Zero
  | Succ e => .Succ $ Expr.subst' x body e
  | NatRec v e0 e1 => 
    .NatRec 
      (Expr.subst' x body v)
      (Expr.subst' x body e0)
      (Expr.subst' (x + 2) (inc_free 2 body) e1)
  | Var v => if x == v then body else .Var v

theorem inc_free_typed (h : Typed Γ e τ) 
  : ∀ α, Typed (α :: Γ) (inc_free'' 1 e) τ := by
  intro β
  unfold inc_free''
  have : β :: Γ = [] ++ β :: Γ := by rfl
  rw [this]; clear this
  have : Γ = [] ++ Γ := by rfl
  rw [this] at h; clear this
  apply map_free_flat_eq h
  · intros x h2
    simpa [add_comm]
  · introv
    have : β :: Γ = [β] ++ Γ := by rfl
    conv => lhs; arg 1; rw [this]
    generalize hv : 1 + v = v';
    simp only [Nat.add_eq]
    conv => lhs; arg 2; rw [hv]
    conv => rhs; arg 2; rw [Nat.eq_sub_of_add_eq' hv]
    apply List.getElem_append_right
    simp
    subst hv
    simp

lemma map_free_eq'
  {Γ : Cx}
  (ht : Typed Γ e τ)
  (x : Var)
  (re : Expr)
  (hmap : ∀ Δ e',
    Typed (Δ ++ Γ) e' γ 
    → Typed (Δ ++ Γ) re γ)
  : Typed Γ (re.subst' x e) τ := by
  -- have : 0 = ([] : Cx).length := rfl
  -- rw [this]; clear this

  induction ht generalizing x re with
  | Lam ht IH => 
    rename Cx => Γ'
    unfold Expr.subst'
    constructor
    apply IH
    intro Δ e' ht'
    sorry

  | App _ _ IH1 IH2 => sorry
  | Zero => constructor
  | Succ _ IH => sorry
  | Rec _ _ _ IHe IH0 IH1 => sorry
  | Var hv => sorry



theorem subst_preservation' (x : Var) 
  (hb : Typed Γ body α) (ht : Typed Γ target τ) 
  : Typed Γ (Expr.subst' x body target) τ := by 
  induction body generalizing Γ target with
  | Lam α e IH => 
    unfold Expr.subst'














    sorry
  | App => sorry
  | Zero => sorry
  | Succ => sorry
  | NatRec => sorry
  | Var => sorry



theorem beta_subst_preservation 
  (hb : Typed Γ (Expr.Lam α body) (Ty.Func α β))
  (he : Typed Γ arg α)
  : Typed Γ (Expr.beta_subst (Expr.Lam α body) arg) β := by
    unfold Expr.beta_subst in_bind DeBruijin.root
    unfold_let
    beta_reduce
    generalize h : (fun v => do
      let depth ← curr_depth
      if depth = v then pure (inc_free depth arg)
        else if depth < v then pure (Expr.Var (v - 1)) else pure (Expr.Var v))
      = f
    unfold_projs at h
    sorry












    -- unfold Expr.map_var









-- def Expr.beta_subst (f : Expr) (e : Expr) (h : f.is_lambda) 
--   : DeBruijin Expr := do



-- theorem beta_subst_eq 
--   : Expr.beta_subst (Expr.Lam α body) e h = Expr.beta_subst' α body e := by
--     constructor

-- def Expr.beta_subst'' (body : Expr) (e : Expr)
--   : DeBruijin Expr := 
--     let f := Expr.Lam Ty.Nat body
--     f.beta_subst e (by simp [Expr.is_lambda])

inductive Step : Expr → Expr → Prop where
  | AppS (h : Expr.value e')
    : Step (Expr.App (Expr.Lam τ e) e') (Expr.beta_subst e e')
  | AppL (h : Step e₁ e₁')
    : Step (Expr.App e₁ e₂) (Expr.App (e₁') e₂)
  | AppR (h : Expr.value e₁) (h2 : Step e₂ e₂')
    : Step (Expr.App e₁ e₂) (Expr.App e₁ e₂')
  | RecZ
    : Step (Expr.NatRec Expr.Zero e0 e1) e0
  | RecE (h : Step e e')
    : Step (Expr.NatRec e e0 e1) (Expr.NatRec e' e0 e1)
  | RecS
    : Step 
      (Expr.NatRec (Expr.Succ e) e0 e1)
      (Expr.beta_subst (Expr.beta_subst e1 (Expr.NatRec e e0 e1)) e)

theorem preservation (ht : Typed [] e τ) (hs : Step e e') : Typed [] e' τ := by
  induction τ with
  | Func α β IHα IHβ => 
    cases hs with
    | AppS v => sorry
    | AppL hs => sorry
    | AppR v1 hs => sorry
    | RecZ => sorry
    | RecE => sorry
    | RecS => sorry
  | Nat => sorry




end SystemT
