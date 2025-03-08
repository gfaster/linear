import Linear.Defs

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

lemma exists_common_of_eq {a b : Ty} 
  (hne : a ≠ b) (h : a ::ₘ Δ₁ = b ::ₘ Δ₂)
  : ∃ Δ, Δ₁ = b ::ₘ Δ ∧ Δ₂ = a ::ₘ Δ := by 
  obtain ⟨Δ, hΔ⟩ := Multiset.exists_cons_of_mem $ mem_of_cons hne h
  exists Δ
  subst hΔ
  rw [Multiset.cons_swap, Eq.comm] at h
  simp at h
  simp [h]

lemma cons_cons_id {Δ₁ Δ₂ : Cx} 
  : a ::ₘ b ::ₘ Δ₁ = c ::ₘ a ::ₘ Δ₂ ↔ b ::ₘ Δ₁ = c ::ₘ Δ₂ := by
    constructor
    · intro h
      nth_rewrite 2 [Multiset.cons_swap] at h
      exact (Multiset.cons_inj_right a).mp h
    · intro h
      nth_rewrite 2 [Multiset.cons_swap]
      solve_by_elim


lemma cons_cons_id' {Δ₁ Δ₂ : Cx}
  : a ::ₘ b ::ₘ Δ₁ = b ::ₘ d ::ₘ Δ₂ ↔ a ::ₘ Δ₁ = d ::ₘ Δ₂ := by
    constructor
    · intro h
      rewrite [Multiset.cons_swap] at h
      exact (Multiset.cons_inj_right b).mp h
    · intro h
      rewrite [Multiset.cons_swap]
      solve_by_elim

lemma rot4' {a b c d : Cx} : a + b + c + d = d + a + b + c := by ac_rfl
lemma rot4 {a b c d : Cx} : a + b + c + d = b + c + d + a := by ac_rfl

lemma cons_rot {Δ : Cx} : a ::ₘ b ::ₘ c ::ₘ Δ = c ::ₘ a ::ₘ b ::ₘ Δ := by
  simp_rw [Multiset.cons_swap]
