import Mathlib.Tactic


def Bool' := forall α, α → α → α
def True' : Bool' := λ _ ↦  λ x ↦ λ _y ↦ x
def False' : Bool' := λ _ ↦ λ _x ↦ λ y ↦ y

section
variable {α : Type}
variable (T E : α)

def if' : Bool' → α := λ b ↦ (b α) T E

theorem if_true' : if' T E True' = T := by
  reduce; rfl

theorem if_false' : if' T E False' = E := by
  reduce; rfl

end

def and' : Bool' → Bool' → Bool' := 
  λ a ↦ λ b ↦ (a _) b False'

theorem and_true_true : and' True' True' = True' := by
  reduce; rfl

theorem and_true_false : and' True' False' = False' := by
  reduce; rfl

theorem and_false_true : and' False' True' = False' := by
  reduce; rfl

theorem and_false_false : and' False' True' = False' := by
  reduce; rfl

def not' : Bool' → Bool' :=
  λ b ↦ (b _) False' True'

theorem not_true' : not' True' = False' := by
  reduce; rfl

theorem not_false' : not' False' = True' := by
  reduce; rfl

