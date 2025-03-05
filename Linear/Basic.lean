import Mathlib.Data.Multiset.Basic

inductive Ty : Type where
  | Plus : Ty → Ty → Ty
  | Tensor : Ty → Ty → Ty
  | Lolly : Ty → Ty → Ty
  | With : Ty → Ty → Ty
  | One

infixr:69 " ⊸ " => Ty.Lolly
infixl:70 " ⊕ " => Ty.Plus
infixl:71 " ⊗ " => Ty.Tensor
infixl:72 " & " => Ty.With

@[reducible]
def Cx : Type := Multiset Ty

inductive Typed : Cx → Ty → Prop where
  | One_R 
    : Typed ∅ Ty.One

  | One_L {Δ : Cx} {C : Ty} 
    : Typed Δ C → Typed (Ty.One ::ₘ Δ) C

  | Tensor_L {Δ : Cx} {A B C : Ty}
    : Typed (A ::ₘ B ::ₘ Δ) C → Typed (A ⊗ B ::ₘ Δ) C

  | Tensor_R {A B : Ty} (Δ₁ Δ₂ : Cx) 
    : Typed Δ₁ A → Typed Δ₂ B → Typed (Δ₁ + Δ₂) (A ⊗ B)

  | Plus_L {Δ : Cx} {A B C : Ty}
    : Typed (A ::ₘ Δ) C → Typed (B ::ₘ Δ) C → Typed ((A ⊕ B) ::ₘ Δ) C

  | Plus_R1 {Δ : Cx} {A B : Ty}
    : Typed Δ A → Typed Δ (A ⊕ B)

  | Plus_R2 {Δ : Cx} {A B : Ty}
    : Typed Δ B → Typed Δ (A ⊕ B)

  | Lolly_L (Δ₁ Δ₂ : Cx) {A B C : Ty}
    : Typed Δ₁ A → Typed (B ::ₘ Δ₂) C → Typed (A ⊸ B ::ₘ (Δ₁ + Δ₂)) C

  | Lolly_R {Δ : Cx} {A B : Ty}
    : Typed (A ::ₘ Δ) B → Typed Δ (A ⊸ B)

  | With_L1 {Δ : Cx} {A B C : Ty}
    : Typed (A ::ₘ Δ) C → Typed (A & B ::ₘ Δ) C

  | With_L2 {Δ : Cx} {A B C : Ty}
    : Typed (B ::ₘ Δ) C → Typed (A & B ::ₘ Δ) C

  | With_R {Δ : Cx} {A B : Ty}
    : Typed Δ A → Typed Δ B → Typed Δ (A & B)


infix:50 " ⊢ " => Typed

syntax "apply_triv" : tactic
macro_rules
  | `(tactic|apply_triv) =>
  `(tactic|
    repeat' (
      first | apply Typed.One_R | apply Typed.One_L | 
        apply Typed.Tensor_L | apply Typed.Lolly_R |
        apply Typed.With_R | apply Typed.Tensor_R
      try simp only [Multiset.cons_zero]
        ) ) 

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


lemma mem_of_cons {Δ1 Δ2 : Cx} {a1 a2 : Ty} 
  : a1 ≠ a2 → a1 ::ₘ Δ1 = a2 ::ₘ Δ2 → a2 ∈ Δ1 := by
  intros hne hce
  have : a2 ∈ a2 ::ₘ Δ2 := Multiset.mem_cons_self a2 Δ2
  rw [←hce] at this
  apply Multiset.mem_cons.mp at this
  cases this with
  | inr => assumption
  | inl h => 
    rw [Eq.comm] at h
    contradiction

lemma cons_mem_of_add {Δ Δ1 Δ2: Cx} {a : Ty} (h : a ::ₘ Δ = Δ1 + Δ2)
  : ∃ Δ', Δ1 = a ::ₘ Δ' ∨ Δ2 = a ::ₘ Δ' := by 
    have : a ∈ Δ1 ∨ a ∈ Δ2 := by
      rw [←Multiset.mem_add, ←h]
      exact Multiset.mem_cons_self _ _
    cases this <;> {
      rename_i hm
      obtain ⟨Δ', hΔ'⟩ := Multiset.exists_cons_of_mem hm;
      exists Δ'
      subst hΔ'
      simp
    }


-- syntax "cut_r_l" tactic : tactic
-- macro_rules
--   | `(tactic|cut_r_l $t1) =>
--   `(tactic|
--     ) 




theorem cut_elim {Δ Δ' : Cx} {A B : Ty} (h1 : Δ ⊢ A) (h2 : A ::ₘ Δ' ⊢ B)
  : Δ + Δ' ⊢ B := by
  induction h1 generalizing Δ' B
  case One_L Δ1 A h3 IH =>
    rw [Multiset.cons_add]
    apply Typed.One_L
    exact IH h2
  case One_R => 
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

      
    repeat sorry
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
      obtain ⟨_, hΔ'2⟩ := Multiset.exists_cons_of_mem (mem_of_cons (by simp) h)
      rw [hΔ'2]
      rw [hΔ'2] at h; repeat (rw [Multiset.cons_swap] at h; simp at h)
      rw [add_comm, Multiset.cons_add]
      apply Typed.One_L

      rw [add_comm]
      apply IH <;> try assumption
    case Lolly_L Δl1 Δl2 la lb lc hla hlc IH IH' => 
      obtain ⟨Δ'2, hΔ'2⟩ := Multiset.exists_cons_of_mem (mem_of_cons _ h)
      subst_vars
      repeat (simp [Multiset.cons_swap] at h)
      rw [add_comm, Multiset.cons_add]
      have : (a & b) ∈ Δl1 ∨ (a & b) ∈ Δl2 := by
        rw [←Multiset.mem_add, ←h]
        exact Multiset.mem_cons_self _ _
      cases this with
      | inl hi =>
        apply Multiset.exists_cons_of_mem at hi
        obtain ⟨Δl1', hΔl1'⟩ := hi
        subst_eqs
        simp at h IH
        subst h
        rw [add_right_comm]
        rw [add_comm] at IH
        apply Typed.Lolly_L <;> assumption
      
      | inr hi => 
        apply Multiset.exists_cons_of_mem at hi
        obtain ⟨Δl1', hΔl1'⟩ := hi
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
    case Tensor_R c d Δc Δd hc hd IH' IH =>

      sorry







      


      


