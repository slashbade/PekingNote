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

-- instance trivial_smul {G α : Type} [Group G] : SMul G α where
--   smul := fun g a => a
-- instance trivial_mul_action {G α : Type} [Group G] : MulAction G α where
--   one_smul := fun _ => rfl
--   mul_smul := fun _ _ _ => rfl
end exp15


/-! Example 1.6 -/
#check ConjAct G
#check ConjAct.units_smul_def
#check ConjAct.unitsMulDistribMulAction

/-! Example 1.7 -/

#check MulAction.quotient
#check MulAction.Quotient.smul_mk

/-! Example 1.8 -/

namespace Stabilizer

variable {A : Type*} [MulAction G A]
#check MulAction.stabilizer
-- def stabilizer (a : α) : Subgroup G :=
--   { MulAction.stabilizerSubmonoid G a with
--     inv_mem' := fun {m} (ha : m • a = a) => show m⁻¹ • a = a by rw [inv_smul_eq_iff, ha] }

def setStabilizer (s : Set A) : Subgroup G := sInf (Set.range (fun a:s => (MulAction.stabilizer G a.1)))
  --Subgroup.of (IsSubgroup.iInter
  --(fun a:s => Subgroup.isSubgroup (MulAction.stabilizer G a.1)) )

end Stabilizer
def MulAction.kernel (G A : Type) [Group G] [MulAction G A] : Subgroup G := Stabilizer.setStabilizer (@Set.univ A)
/-! Example 1.9 -/
namespace Kernel

variable [MulAction G A]
open Stabilizer

lemma mem_kernel_iff {x : G} {A : Type} [MulAction G A] : x ∈ MulAction.kernel G A ↔ ∀ a : A, x • a = a := by
  constructor
  · intro h a
    simp only [MulAction.kernel,Set.mem_range,setStabilizer] at h
    simp only [Subgroup.mem_sInf, Set.mem_range, Subtype.exists, Set.mem_univ, exists_const,
      forall_exists_index, forall_apply_eq_imp_iff, MulAction.mem_stabilizer_iff] at h
    exact h a
  · intro h
    simp only [MulAction.kernel,setStabilizer]
    simp only [Subgroup.mem_sInf, Set.mem_range, Subtype.exists, Set.mem_univ, exists_const,
      forall_exists_index, forall_apply_eq_imp_iff, MulAction.mem_stabilizer_iff]
    assumption

lemma kernel_of_permHom : MonoidHom.ker (MulAction.toPermHom G A) = MulAction.kernel G A := by
  ext x
  rw [MonoidHom.mem_ker,mem_kernel_iff]
  constructor
  · simp
    intro h a
    rw [←MulAction.toPerm_apply x a,h]
    rfl
  · simp only [MulAction.toPermHom_apply]
    intro h
    ext y
    simp only [MulAction.toPerm_apply]
    exact h y

instance MulAction.kernel.normal : (MulAction.kernel G A).Normal := by
  rw [←kernel_of_permHom]
  exact MonoidHom.normal_ker (MulAction.toPermHom G A)

end Kernel

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
