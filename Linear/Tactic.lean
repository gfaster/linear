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
  | `(tactic|simp_cx $l?) =>
  `(tactic| 
    simp [] $l?; -- put it in the simp normal form
    (iterate 2 try (rewrite [cons_rot] $l?; simp [] $l?));
    (try (rw [Multiset.cons_swap] $l?; simp [] $l?));
    try simp [] $l?; -- put it back in normal form
  ) 
