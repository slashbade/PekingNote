import Mathlib.Algebra.Group.Centralizer

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Deprecated.Subgroup
import Mathlib.GroupTheory.QuotientGroup

open Classical

variable {G α : Type} [Group G]
variable {H : Subgroup G}

-- #check MulAction G M

/-! Example 1.1 -/
instance : MulAction (Equiv.Perm M) M where
  one_smul := Equiv.Perm.one_apply
  mul_smul := Equiv.Perm.mul_apply

#check Function.End.applyMulAction
/-! Example 1.2-/
instance : MulAction G G where
  one_smul := one_mul
  mul_smul := mul_assoc

/-! Example 1.3 -/
#check MulAction.toPermHom
#check MulAction.bijective
#check MulAction.toPerm_injective

/-! Example 1.5 -/
namespace exp15

instance trivial_smul {G α : Type} [Group G] : SMul G α where
  smul := fun g a => a
instance trivial_mul_action {G α : Type} [Group G] : MulAction G α where
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
end exp15


/-! Example 1.6 -/
#check ConjAct G
#check ConjAct.units_smul_def
#check ConjAct.unitsMulDistribMulAction

/-! Example 1.7 -/

#check MulAction.quotient
#check MulAction.Quotient.smul_mk

/-! Example 1.8 -/



/-! Example 1.10 -/
namespace Center

#check Subgroup.centralizer
#check Subgroup.center
#check Subgroup.normalizer

end Center

/-! Example 1.12 -/
namespace exp12

lemma exp121 {G:Type} [CommGroup G] : ∀ (A : Set G), Subgroup.centralizer A = ⊤ := by
  intro A
  simp only [Subgroup.centralizer_eq_top_iff_subset,CommGroup.center_eq_top]
  simp only [Subgroup.coe_top, Set.subset_univ]
end exp12
