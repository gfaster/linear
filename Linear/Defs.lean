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

  | Tensor_R {Δ₁ Δ₂ : Cx} {A B : Ty}  
    : Typed Δ₁ A → Typed Δ₂ B → Typed (Δ₁ + Δ₂) (A ⊗ B)

  | Plus_L {Δ : Cx} {A B C : Ty}
    : Typed (A ::ₘ Δ) C → Typed (B ::ₘ Δ) C → Typed ((A ⊕ B) ::ₘ Δ) C

  | Plus_R1 {Δ : Cx} {A B : Ty}
    : Typed Δ A → Typed Δ (A ⊕ B)

  | Plus_R2 {Δ : Cx} {A B : Ty}
    : Typed Δ B → Typed Δ (A ⊕ B)

  | Lolly_L {Δ₁ Δ₂ : Cx} {A B C : Ty}
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
