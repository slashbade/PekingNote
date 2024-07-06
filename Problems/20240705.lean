import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

noncomputable section

namespace Example1103B

variable {α : Type}
structure Sym (S : Set α) where
  Fun : {x // x ∈ S} → {x // x ∈ S}
  invFun : {x // x ∈ S} → {x // x ∈ S}
  left_inv : ∀ x : {x // x ∈ S}, invFun (Fun x) = x
  right_inv : ∀ x : {x // x ∈ S}, Fun (invFun x) = x

structure Sym' {S T : Set α} (h : T ⊆ S) extends Sym S where
  T_invariant : ∀ x : {x // x ∈ T}, Fun ((fun ⟨x, xt⟩ ↦ ⟨x, h xt⟩) x) = (fun ⟨x, xt⟩ ↦ ⟨x, h xt⟩) x

instance (S : Set α): Group (Sym S) where
  mul := fun f g ↦ {
    Fun := fun (x : {x // x ∈ S}) ↦ f.Fun (g.Fun x)
    invFun := fun (x : {x // x ∈ S}) ↦ g.invFun (f.invFun x)
    left_inv := fun ⟨x, xs⟩ ↦ ( by
      dsimp
      have : f.invFun (f.Fun (g.Fun ⟨x, xs⟩)) = g.Fun ⟨x, xs⟩ := by apply Sym.left_inv
      rw [this]; apply Sym.left_inv
    )
    right_inv := fun ⟨x, xs⟩ ↦ ( by
      dsimp
      have : g.Fun (g.invFun (f.invFun ⟨x, xs⟩)) = f.invFun ⟨x, xs⟩ := by apply Sym.right_inv
      rw [this]; apply Sym.right_inv
    )
  }
  mul_assoc := by
    intro a b c
    dsimp [(· * ·)]
  one := {
    Fun := id
    invFun := id
    left_inv := by simp only [id_eq, implies_true]
    right_inv := by simp only [id_eq, implies_true]
  }
  one_mul := by
    intro a
    rfl
  mul_one := by
    intro a
    rfl
  inv := fun f ↦ ⟨f.invFun, f.Fun, f.right_inv, f.left_inv⟩
  mul_left_inv := by
    intro a
    unfold_projs
    dsimp
    simp only [Sym.mk.injEq, and_self]
    funext x
    rw [a.left_inv]; rfl

instance (S T : Set α) {ssubt : T ⊆ S} : Group (Sym' ssubt) where
  mul := fun f g ↦ {
    Fun := fun (x : {x // x ∈ S}) ↦ f.Fun (g.Fun x)
    invFun := fun (x : {x // x ∈ S}) ↦ g.invFun (f.invFun x)
    left_inv := by
      intro x
      dsimp
      have : f.invFun (f.Fun (g.Fun x)) = g.Fun x := by apply Sym.left_inv
      rw [this]
      exact g.left_inv x
    right_inv := by
      intro x
      dsimp
      have : g.Fun (g.invFun (f.invFun x)) = f.invFun x := by apply Sym.right_inv
      rw [this]
      exact f.right_inv x
    T_invariant := by
      intro x
      dsimp
      ext; dsimp
      simp only [g.T_invariant, f.T_invariant]
  }
  mul_assoc := by
    intro a b c
    rfl
  one := {
    Fun := id
    invFun := id
    left_inv := by
      intro x
      rfl
    right_inv := by
      intro x
      rfl
    T_invariant := by
      intro hx
      rfl
  }
  one_mul := by
    intro a
    rfl
  mul_one := by
    intro a
    rfl
  inv :=
   fun f ↦ {
    Fun := f.invFun
    invFun := f.Fun
    right_inv := by
      intro x
      exact f.left_inv x
    left_inv := by
      intro x
      exact f.right_inv x
    T_invariant := by
      intro x
      dsimp
      -- unfold Sym.invFun
      -- unfold Sym'.toSym
      -- rw [Subtype.mk_eq_mk]
      have aa := (f.T_invariant x).symm
      simp at aa
      have h1 := congr_arg f.invFun aa
      rw [f.left_inv] at h1
      exact h1


  }
  mul_left_inv := by
    intro a
    dsimp [(· * ·)]
    simp only [a.left_inv]
    rfl

instance (S T : Set α) (ssubt : S ⊆ T) : Sym (S \ T) ≃* Sym' ssubt where
  toFun := fun f ↦ {
    sorry
  }
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

variable {α : Type*}
variable (S T : Set α)
open Set
example {x : α} (h : T ⊆ S) (b : x ∈ T) : x ∈ S := by
  exact h b
