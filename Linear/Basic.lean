import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Abel
import Linear.Defs
import Linear.Lemmas
import Linear.Tactic


-- syntax "apply_triv1" : tactic
-- macro_rules
--   | `(tactic|apply_triv1) =>
--   `(tactic|
--     solve_by_elim [
--       Typed.One_R,
--       Typed.One_L,
--       Typed.Tensor_L,
--       Typed.Lolly_R,
--       Typed.With_R 
--     ]
--  ) 

-- open Lean.Elab.Tactic in
-- elab "exhaust_ty" : tactic =>
--   withMainContext do
--     let _goal ← getMainGoal



@[simp]
theorem typed_id : {a} ⊢ a := by
  induction a with
  | One => apply_triv
  | Plus a b => 
    apply Typed.Plus_L <;> simp
    apply Typed.Plus_R1 ; assumption
    apply Typed.Plus_R2 ; assumption
  | Tensor a b => 
    apply_triv
    apply Typed.Tensor_R {a} {b} <;> assumption
  | With a b => 
    apply_triv
    apply Typed.With_L1
    simp
    assumption
    apply Typed.With_L2
    simp
    assumption
  | Lolly a b => 
    apply_triv
    show {a, a ⊸ b} ⊢ b
    rw [Multiset.pair_comm a (a ⊸ b)]
    apply Typed.Lolly_L {a} {} <;> assumption








-- syntax "cut_r_l" tactic : tactic
-- macro_rules
--   | `(tactic|cut_r_l $t1) =>
--   `(tactic|
--     ) 

/-
The individual proofs typically follow at least one of the following forms, in
order:

1. h is of the form `a ::ₘ Δ₁ = b ::ₘ Δ₂` where `a ≠ b`
  - we want to introduce Δ as a common context using `exists_common_of_eq`


-/

lemma cut_elim_one_r (h2 : Ty.One ::ₘ Δ' ⊢ B) : ∅ + Δ' ⊢ B := by
  generalize h : Ty.One ::ₘ Δ' = Δ'' at h2
  induction h2 generalizing Δ'
  case One_R => 
    absurd h
    exact Multiset.cons_ne_zero
  case One_L a b c d => 
    simp at *
    rw [h]
    exact c
  case Tensor_L Δ2 c d b2 hb2 IH3 =>
    simp at *
    have : c ⊗ d ∈ Δ' := mem_of_cons (by simp) h
    obtain ⟨Δ'2, hΔ'2⟩ := Multiset.exists_cons_of_mem this
    rw [hΔ'2]
    apply Typed.Tensor_L
    apply IH3
    rw [Multiset.cons_swap]; simp
    rw [Multiset.cons_swap]; simp
    rw [hΔ'2] at h
    rw [Multiset.cons_swap] at h; simp at h
    assumption
  case Tensor_R c d Δt1 Δt2 hc hd IH IH' =>
    simp at *
    obtain ⟨Δ, hΔ⟩ := cons_mem_of_add h
    cases hΔ <;> {
      subst_vars
      simp at h IH IH'
      subst h
      constructor <;> assumption
    }
  case Plus_L IH IH' =>
    obtain ⟨_, hΔ'2⟩ := Multiset.exists_cons_of_mem (mem_of_cons (by simp) h)
    subst hΔ'2; repeat (rw [Multiset.cons_swap] at h; simp at h)
    simp
    subst h
    rw [Multiset.cons_swap] at IH IH'
    simp at IH IH'
    constructor <;> assumption
  case Plus_R1 IH =>
    apply Typed.Plus_R1
    subst h
    simp at IH
    simp [IH]
  case Plus_R2 IH =>
    apply Typed.Plus_R2
    subst h
    simp at IH
    simp [IH]
    
  repeat1 sorry

theorem cut_elim {Δ Δ' : Cx} {A B : Ty} (h1 : Δ ⊢ A) (h2 : A ::ₘ Δ' ⊢ B)
  : Δ + Δ' ⊢ B := by
  induction h1 generalizing Δ' B
  case One_L Δ1 A h3 IH =>
    rw [Multiset.cons_add]
    apply Typed.One_L
    exact IH h2
  case One_R => exact cut_elim_one_r h2
  case With_R Δ1 a b ha hb IH1 IH2 =>
    generalize h : (a & b) ::ₘ Δ' = Δ'' at h2
    induction h2 generalizing Δ'
    case Tensor_L Δ2 c d b2 hb2 IH3 =>
      -- have := mem_of_cons (by simp) h
      -- type specifier here is unnecessary
      have : c ⊗ d ∈ Δ' := mem_of_cons (by simp) h
      obtain ⟨Δ'2, hΔ'2⟩ := Multiset.exists_cons_of_mem this
      rw [hΔ'2]
      rw [add_comm, Multiset.cons_add]
      apply Typed.Tensor_L
      rw [←Multiset.cons_add, ←Multiset.cons_add, add_comm]
      apply IH3 <;> try assumption
      rw [Multiset.cons_swap]; simp
      rw [Multiset.cons_swap]; simp
      rw [hΔ'2] at h
      rw [Multiset.cons_swap] at h; simp at h
      assumption

    case Plus_L IH IH' =>
      -- have := mem_of_cons (by simp) h
      -- type specifier here is unnecessary
      have := mem_of_cons (by simp) h
      obtain ⟨Δ'2, hΔ'2⟩ := Multiset.exists_cons_of_mem this
      rw [hΔ'2]
      rw [add_comm, Multiset.cons_add]
      apply Typed.Plus_L
      rw [←Multiset.cons_add, add_comm]
      apply IH <;> try assumption
      rw [Multiset.cons_swap]; simp
      rw [hΔ'2] at h
      rw [Multiset.cons_swap] at h; simp at h
      assumption
      rw [←Multiset.cons_add, add_comm]
      apply IH' <;> try assumption
      rw [Multiset.cons_swap]; simp
      rw [hΔ'2] at h
      rw [Multiset.cons_swap] at h; simp at h
      assumption
    case One_R => simp at h
    case One_L IH =>
      -- canonical basic case
      obtain ⟨_, hΔ'2⟩ := Multiset.exists_cons_of_mem (mem_of_cons (by simp) h)
      subst hΔ'2; repeat (rw [Multiset.cons_swap] at h; simp at h)
      rw [add_comm, Multiset.cons_add]
      apply Typed.One_L

      rw [add_comm]
      apply IH <;> assumption
    case Lolly_L Δl1 Δl2 la lb lc hla hlc IH IH' => 
      obtain ⟨Δ'2, hΔ'2⟩ := Multiset.exists_cons_of_mem (mem_of_cons _ h)
      subst_vars
      repeat (simp [Multiset.cons_swap] at h)
      rw [add_comm, Multiset.cons_add]
      obtain ⟨Δl1', hΔl1'⟩ := cons_mem_of_add h
      cases hΔl1' with
      | inl hi =>
        subst_eqs
        simp at h IH
        subst h
        rw [add_right_comm]
        rw [add_comm] at IH
        apply Typed.Lolly_L <;> assumption
      | inr hi => 
        subst_eqs
        simp at h
        subst h
        rw [add_right_comm, add_assoc]
        apply Typed.Lolly_L <;> try assumption
        rw [add_comm, ←Multiset.cons_add, add_comm]
        apply IH'
        simp [Multiset.cons_swap]
      

    case With_L1 Δ c d _ _ IH =>
      by_cases he : c & d ≠ a & b 
      case pos =>
        obtain ⟨_, hΔ'2⟩ := Multiset.exists_cons_of_mem (mem_of_cons _ h)
        rw [hΔ'2]
        rw [hΔ'2] at h; repeat (rw [Multiset.cons_swap] at h; simp at h)
        rw [add_comm, Multiset.cons_add]
        apply Typed.With_L1
        rw [←Multiset.cons_add, add_comm]
        apply IH <;> try assumption
        rw [Multiset.cons_swap];
        simp
        assumption
      case neg =>
        simp at he
        obtain ⟨ha, hb⟩ := he
        subst_vars
        simp at h
        subst_eqs
        apply IH1
        assumption
    case With_L2 Δ c d _ _ IH =>
      by_cases he : c & d ≠ a & b 
      case pos =>
        obtain ⟨_, hΔ'2⟩ := Multiset.exists_cons_of_mem (mem_of_cons _ h)
        rw [hΔ'2]
        rw [hΔ'2] at h; repeat (rw [Multiset.cons_swap] at h; simp at h)
        rw [add_comm, Multiset.cons_add]
        apply Typed.With_L2
        rw [←Multiset.cons_add, add_comm]
        apply IH <;> try assumption
        rw [Multiset.cons_swap];
        simp
        assumption
      case neg =>
        simp at he
        obtain ⟨ha, hb⟩ := he
        subst_vars
        simp at h
        subst_eqs
        apply IH2
        assumption
    case Tensor_R c d Δc Δd hc hd IH IH' =>
      obtain ⟨Δ, hΔ⟩ := cons_mem_of_add h
      cases hΔ with
      | inl hc =>
        subst hc
        simp at h IH
        subst h
        rw [←add_assoc]
        apply Typed.Tensor_R <;> assumption
      | inr hc => 
        subst hc
        simp at h IH IH'
        subst h
        rw [←add_comm, add_right_comm, add_assoc]
        apply Typed.Tensor_R <;> assumption
    case Plus_R1 Δ c d hc IH => 
      apply Typed.Plus_R1
      exact IH h
    case Plus_R2 Δ c d hc IH => 
      apply Typed.Plus_R2
      exact IH h
    case Lolly_R Δ c d hc IH =>
      apply Typed.Lolly_R
      rw [add_comm, ←Multiset.cons_add, add_comm]
      apply IH
      simp [Multiset.cons_swap]
      assumption
    case With_R Δ c d hc hd IH IH' => 
      apply Typed.With_R
      exact IH h
      exact IH' h
  case Tensor_R a b Δt1 Δt2 ha hb IH1_outer IH2_outer =>
    generalize h : (a ⊗ b) ::ₘ Δ' = Δ'' at h2
    generalize ht : Δt1 + Δt2 = Δt at *
    induction h2 generalizing Δ'
    case Lolly_L Δl1 Δl2 la lb lc hla hlc IH IH' => 
      let ⟨Δ, ⟨hΔ1, hΔ2⟩⟩ := exists_common_of_eq (by simp) h
      subst hΔ1
      obtain ⟨Δ, ⟨hΔ'⟩⟩ := cons_mem_of_add (Eq.symm hΔ2)
      case inl =>
        subst hΔ'
        simp at hΔ2; subst hΔ2
        clear h
        simp at *
        -- what I want to be able to do is automatically put the goal in a form
        -- that can be unified with IH, but I haven't quite figured that out.
        -- My best guess is a tactic that looks at the de-generalized IH and
        -- the Typed constructor to re-apply, but that seems clearly wrong
        rw [←add_assoc]
        apply Typed.Lolly_L <;> assumption
      case inr hΔ' => -- I have no clue why it isn't bound here automatically
        subst hΔ'
        simp at hΔ2; subst hΔ2
        clear h
        rw [Multiset.cons_swap] at IH'
        simp at *
        rw [add_left_comm]
        apply Typed.Lolly_L <;> assumption
    case One_R => absurd h; simp
    case One_L IH =>
      let ⟨Δ, ⟨hΔ1, hΔ2⟩⟩ := exists_common_of_eq (by simp) h
      subst hΔ1
      subst hΔ2
      simp at *
      apply Typed.One_L <;> assumption
    case Tensor_L Δ c d e he IH =>
      -- every case that's the inverse of the outer needs the by_cases
      by_cases heq : a ⊗ b ≠ c ⊗ d
      case pos =>
        let ⟨Δ, ⟨hΔ1, hΔ2⟩⟩ := exists_common_of_eq heq h
        substs hΔ1 hΔ2
        clear h
        rw [cons_rot] at IH
        simp at IH
        rw [add_comm, Multiset.cons_add, add_comm]
        apply Typed.Tensor_L <;> assumption
      case neg =>
        clear IH -- impossible to satisfy
        simp at heq
        obtain ⟨x, x⟩ := heq; subst_vars
        simp at h; subst h
        rw [add_assoc, add_left_comm]
        apply_assumption
        rw [add_comm, ←Multiset.cons_add, add_comm]
        apply_assumption
        assumption
    case Tensor_R IH1 IH2 =>
      obtain ⟨Δ, ⟨hΔ⟩⟩ := cons_mem_of_add h
      case inl =>
        subst hΔ
        simp at h
        subst h
        simp at IH1
        rw [←add_assoc]
        constructor <;> solve_by_elim
      case inr hΔ =>
        subst hΔ
        simp at h
        subst h
        rw [add_left_comm]
        constructor <;> solve_by_elim
    case Plus_L IH1 IH2 =>
      let ⟨Δ, ⟨hΔ1, hΔ2⟩⟩ := exists_common_of_eq (by simp) h
      substs hΔ1 hΔ2
      clear h -- trivial
      rw [Multiset.cons_swap] at IH1 IH2; simp at IH1 IH2
      simp
      constructor <;> assumption
    case Plus_R1 IH1 IH2 => solve_by_elim [Typed.Plus_R1]
    case Plus_R2 IH1 IH2 => solve_by_elim [Typed.Plus_R2]
    case With_L1 IH =>
      let ⟨Δ, ⟨hΔ1, hΔ2⟩⟩ := exists_common_of_eq (by simp) h
      substs hΔ1 hΔ2
      clear h
      rw [Multiset.cons_swap] at IH; simp at IH
      simp
      -- can omit this apply since it's the first ctor
      -- apply Typed.With_L2
      solve_by_elim
    case With_L2 IH =>
      let ⟨Δ, ⟨hΔ1, hΔ2⟩⟩ := exists_common_of_eq (by simp) h
      substs hΔ1 hΔ2
      clear h
      rw [Multiset.cons_swap] at IH; simp at IH
      simp
      apply Typed.With_L2
      solve_by_elim
    case With_R IH1 IH2 =>
      subst h
      simp at IH1 IH2
      solve_by_elim
    case Lolly_R IH =>
      subst h
      rw [Multiset.cons_swap] at IH; simp at IH
      solve_by_elim
  case Tensor_L Δ a b c IH1_outer IH2_outer =>
    simp at IH2_outer
    generalize h : c ::ₘ Δ' = Δ'' at h2
    induction h2 generalizing Δ'
    case One_R => absurd h; simp
    case One_L IH => 
      by_cases hne: c ≠ Ty.One
      let ⟨Δ, ⟨hΔ1, hΔ2⟩⟩ := exists_common_of_eq hne h
      case pos =>
        substs hΔ1 hΔ2
        clear h
        simp at IH
        simp; solve_by_elim
      case neg =>
        clear IH
        simp at hne
        subst hne
        simp at h
        subst h
        rw [Multiset.cons_add]
        constructor
        solve_by_elim
    case Tensor_L d e f g h IH =>
      by_cases hne: c ≠ e ⊗ f
      case pos =>
        let ⟨Δ, ⟨hΔ1, hΔ2⟩⟩ := exists_common_of_eq hne h
        subst_vars
        clear h
        -- rw [cons_rot] at IH; simp at IH
        simp_cx at IH




        -- simp; constructor
        -- rw [cons_rot]
        -- assumption
      case neg =>
        simp at hne
        subst hne
        simp at h
        subst h
        simp; constructor
        solve_by_elim
    case Tensor_R IH1 IH2 =>
      obtain ⟨Δ, ⟨hΔ⟩⟩ := cons_mem_of_add h
      case inl =>
        subst hΔ
        simp at h
        subst h
        simp at IH1 IH2
        rw [←add_assoc]
        -- while solve_by_elim or constructor frequently works, it's more
        -- reliable to apply the specific case
        apply Typed.Tensor_R
        · simp; assumption
        · solve_by_elim
      case inr hΔ =>
        subst hΔ
        simp at h
        subst h
        simp at IH1 IH2
        rw [←add_assoc]
        apply Typed.Tensor_R


