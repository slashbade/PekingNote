import Mathlib.Algebra.Group.Centralizer

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup

open Classical

variable {G α : Type} [Group G]
variable {H : Subgroup G}

-- #check MulAction G M

/-! Example 1.1 -/
instance : MulAction (Equiv.Perm M) M where
  one_smul := Equiv.Perm.one_apply
  mul_smul := Equiv.Perm.mul_apply

/-! Example 1.2-/
instance : MulAction G G where
  one_smul := one_mul
  mul_smul := mul_assoc

/-! Example 1.5 -/
namespace exp15
instance trivial_smul : SMul G α where
  smul := fun g a => a
instance trivial_mul_action : MulAction G α where
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
end exp15


/-! Example 1.6 -/
#check ConjAct G


/-!Example 1.7-/
namespace exp17
variable (g : G)
variable (gH : G⧸H)
#check QuotientGroup.mk⁻¹

lemma exist_rep : ∃ g : G, QuotientGroup.mk g = gH := by
  rcases gH with g | _
  exact ⟨g, rfl⟩

noncomputable def smul (α : G) (gH : G⧸H) : G⧸H := QuotientGroup.mk (α * choose (exist_rep gH))

noncomputable instance quotient_smul : SMul G (G⧸H) where
  smul := smul

lemma one_smul : (1 : G) • gH = gH := by sorry

lemma mul_smul : ∀ (g₁ g₂ : G) (gH : G⧸H), (g₁ * g₂) • gH = g₁ • g₂ • gH := by
  intro g₁ g₂ gH
  rcases gH with g | Hg
  simp only [quotient_smul, QuotientGroup.mk, choose]
  sorry

noncomputable instance quotient_mul_action : MulAction G (G⧸H) where
  one_smul := one_smul
  mul_smul := mul_smul

def smul_map_permutation (g : G) : Equiv.Perm (G⧸H) := sorry

end exp17

/-! Example 1.12 -/
namespace exp12

lemma exp121 [CommGroup G] : ∀ (A : Set G), Set.centralizer A = G := sorry

end exp12
