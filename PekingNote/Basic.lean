import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct

variable {G α : Type} [Group G]

-- #check MulAction G M

/-! Example 1.1 -/
instance : MulAction (Equiv.Perm M) M where
  one_smul := Equiv.Perm.one_apply
  mul_smul := Equiv.Perm.mul_apply

/-! Example 1.2-/
instance : MulAction G G where
  one_smul := one_mul
  mul_smul := mul_assoc

/-! Example 1.3 -/
#check MulAction.toPermHom
#check MulAction.bijective
#check MulAction.toPerm_injective

/-! Example 1.5 -/
instance trivial_smul : SMul G α where
  smul := fun g a => a
instance trivial_mul_action : MulAction G α where
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

/-! Example 1.6 -/
#check ConjAct G
