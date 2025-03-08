import Lean
import Lean.Parser.Syntax
import Lean.Parser.Tactic
import Linear.Defs
import Linear.Lemmas

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

syntax "simp_cx " (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic|simp_cx $(l)?) =>
  `(tactic|(
    (try simp [] $(l)?); -- put it in the simp normal form
    (iterate 2 try (rewrite [cons_rot] $(l)?; simp [] $(l)?));
    (try (rw [Multiset.cons_swap] $(l)?; simp [] $(l)?));
    try simp [] $(l)?; -- put it back in normal form

    -- try (rw [cons_cons_id, cons_cons_id'] $(l)?);
    -- simp [] $(l)?; -- put it back in normal form
  )) 

-- elab "case_start " $hyp:ident : tactic =>
--   Lean.Elab.Tactic.withMainContext do
    
syntax "case_start_add " term: tactic
macro_rules
  | `(tactic|case_start_add $hyp) =>
    `(tactic|(
      -- second case: a :: Δ = Δ₁ + Δ₂
      first
        | let c := cons_mem_of_add $hyp
        | let c := cons_mem_of_add (Eq.symm $hyp)
        | fail "Not of form for cons_mem_of_add"
      obtain ⟨Δ, ⟨hΔ⟩⟩ := c <;> (
        subst_vars;
        try (simp_cx at $hyp:term; subst $hyp);
        try simp_cx at *;
        try solve_by_elim
      )
    ))

syntax "case_start_common_var " term: tactic
macro_rules
  | `(tactic|case_start_common_var $hyp) =>
    `(tactic|(
      -- the first case is the most common: we need to find a common base case
      -- If this fails, it typically means one of two things: the `by_simp`
      -- case failed (it's non-trivial) that the cons'd elements are not
      -- equal), or it's of the wrong form (typically: a :: Δ = Δ₁ + Δ₂)
      (have ⟨Δ, ⟨hΔ1, hΔ2⟩⟩ := exists_common_of_eq (by simp) $hyp);
      -- sometimes these fail since hΔ1 or hΔ2 is not a variable
      (first | subst hΔ1 | case_start_add hΔ1 | skip);
      (first | subst hΔ2 | case_start_add hΔ2 | skip);
      (try clear $hyp);
      (try simp);
      (try simp_cx at *);
      (try solve_by_elim)
    ))

syntax "case_start_simple" : tactic
macro_rules
  | `(tactic|case_start_simple) =>
    `(tactic|{
      try simp_cx at *;
      subst_vars;
      try simp_cx at *;
      try simp
      try solve_by_elim
    })

syntax "case_start " term: tactic
macro_rules
  | `(tactic|case_start $hyp) =>
    `(tactic|first 
      | {absurd $hyp ; simp}
      | case_start_simple
      | case_start_common_var $hyp 
      | case_start_add $hyp 
      | fail "no good start")


lemma case_start_test (h2 : Ty.One ::ₘ Δ' ⊢ B) : ∅ + Δ' ⊢ B := by
  generalize h : Ty.One ::ₘ Δ' = Δ'' at h2
  induction h2 generalizing Δ'
  case Plus_L IH IH' => case_start h
  case One_R => case_start h
  case One_L a b c d => case_start h
  case Tensor_L Δ2 c d b2 hb2 IH3 => case_start h
  case Tensor_R c d Δt1 Δt2 hc hd IH IH' => case_start h
  case Plus_R1 => solve_by_elim [Typed.Plus_R1]
  case Plus_R2 => solve_by_elim [Typed.Plus_R2]
  case Lolly_L => case_start h
  case Lolly_R IH => case_start h
  case With_L1 => case_start h
  case With_L2 => case_start h; solve_by_elim [Typed.With_L2]
  case With_R => case_start h

