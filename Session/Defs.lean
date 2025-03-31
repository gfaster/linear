import Mathlib.Data.Fintype.Basic

@[reducible]
def Var := Type

inductive Process where
  | Choice (x : Var) {ι : Type} [Fintype ι] (k : ι) : Process → Process
  | Case (x : Var) (ι : Type) [Fintype ι] (f : ι → Process): Process
  | Send (x t : Var) : Process → Process
  | Recv (t x : Var) : Process → Process
  | Close (x : Var) : Process
  | Wait (x : Var) : Process → Process
  | Forward (y x : Var) : Process
  | Spawn (f : Var) (a : List Var) : Process → Process

section
variable (decls : Type) [Fintype decls]
inductive Ty where
  | Var (v : decls)
  -- ⊕{ l : A } l ∈ A
  | InternalChoice (ι : Type) [Fintype ι] (f : ι → Ty) : Ty
  -- &{ l : A } l ∈ A
  | ExternalChoice (ι : Type) [Fintype ι] (f : ι → Ty) : Ty
  | Tensor (a : Ty) (b : Ty) : Ty
  | Lolli (a : Ty) (b : Ty) : Ty
  | One
end

#check Ty


inductive AllDecls where
  | PNat

instance AllDecls.instFintype : Fintype AllDecls := 
  ⟨⟨{PNat}, by simp⟩, fun x => by cases x <;> simp⟩

inductive PVars where
  | Succ
  | Zero

instance PVars.instFintype : Fintype PVars := 
  ⟨⟨{Succ, Zero}, by simp⟩, fun x => by cases x <;> simp⟩

def PNat : Ty AllDecls :=
  Ty.InternalChoice PVars (fun k => match k with
    | .Succ => Ty.Var AllDecls.PNat
    | .Zero => Ty.One
  )

