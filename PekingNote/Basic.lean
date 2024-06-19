import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Deprecated.Subgroup

variable {G α A: Type*} [Group G] {f : G × A → A}

-- #check MulAction G M

/-! Example 1.1 -/
instance : MulAction (Equiv.Perm M) M where
  one_smul := Equiv.Perm.one_apply
  mul_smul := Equiv.Perm.mul_apply

-- instance Function.uncurry_smul {f : G × A → A} : SMul G A where
--   smul := f.curry

-- class uncurry_IsAction (f : G × A → A) where
--   one_smul' : ∀ a : A, f (1,a) = a
--   mul_smul' : ∀ x y : G, ∀ a : A, f (x, (f (y,a))) = f (x*y, a)

-- instance Function.uncurry_action [uncurry_IsAction f]: MulAction G A where
--   smul := f.curry
--   one_smul := sorry
--   mul_smul := sorry

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
-- namespace trivial_action

-- instance trivial_smul : SMul G α where
--   smul := fun g a => a
-- instance trivial_mul_action : MulAction G α where
--   one_smul := fun _ => rfl
--   mul_smul := fun _ _ _ => rfl

-- end trivial_action

/-! Example 1.6 -/
#check ConjAct G
#check ConjAct.units_smul_def
#check ConjAct.unitsMulDistribMulAction

/-! Example 1.7 -/

#check MulAction.quotient
#check MulAction.Quotient.smul_mk

/-! Example 1.8 -/

namespace Stabilizer

variable [MulAction G α]
#check MulAction.stabilizer
-- def stabilizer (a : α) : Subgroup G :=
--   { MulAction.stabilizerSubmonoid G a with
--     inv_mem' := fun {m} (ha : m • a = a) => show m⁻¹ • a = a by rw [inv_smul_eq_iff, ha] }

def stabilizer_of_subset (s : Set α) : Subgroup G := Subgroup.of (IsSubgroup.iInter
  (fun a:s => Subgroup.isSubgroup (MulAction.stabilizer G a.1)) )

def kernel [MulAction G A] : Subgroup G := stabilizer_of_subset (@Set.univ A)

end Stabilizer

/-! Example 1.9 -/
namespace Kernel

variable [MulAction G A]
open Stabilizer

#synth SMul G A  --how to cancel the efftct of a instance which has been registered in Example 1.5?
lemma Subgroup.mem_of_IsSubgroup {x : G} {s : Set G} (h : IsSubgroup s): x ∈ Subgroup.of h ↔ x ∈ s := by
  sorry

lemma mem_kernel_iff {x : G} : x ∈ kernel (A:=A) ↔ ∀ a : A, x • a = a := by
  constructor
  · intro h a
    simp only [kernel,Set.mem_range,stabilizer_of_subset] at h
    rw [Subgroup.mem_of_IsSubgroup] at h
    simp only [Set.mem_iInter] at h
    exact h ⟨a,by simp⟩
  · intro h
    simp only [kernel,Set.mem_range,stabilizer_of_subset,Subgroup.mem_of_IsSubgroup,Set.mem_iInter]
    intro a
    simp --try simp?
    exact  h a.1

lemma kernel_of_permHom : MonoidHom.ker (MulAction.toPermHom G A) = kernel (A:=A) := by
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
end Kernel

/-! Example 1.10 -/
namespace Center

#check Subgroup.centralizer
#check Subgroup.center
#check Subgroup.normalizer

end Center


/-! Example 1.11 -/

/-! Example 1.12 -/


/-! Example 1.13 -/


/-! Example 1.14 -/



/-! Example 1.15 -/


/-! Example 1.16 -/



/-! Example 1.17 -/


/-! Example 1.18 -/

/-! Example 1.19 -/


/-! Example 1.20 -/



/-! Example 1.21 -/


/-! Example 1.22 -/



/-! Example 1.23 -/



/-! Example 1.24 -/




/-! Example 1.25 -/
