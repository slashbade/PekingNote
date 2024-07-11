import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

open Equiv.Perm
lemma Equiv.Perm.perm_entry_eq_of_conj_perm (n : ℕ) (σ : Perm <| Fin n) (l : List <| Fin n)
  (hnd : l.Nodup) : σ * l.formPerm * σ⁻¹ = (l.map σ).formPerm := sorry

open Pointwise
def Group.product_mul_equiv_of_normal_disjoint {G : Type*}
  [Group G] (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal] (hnd : H.carrier ∩ K = ⊥) :
  (H * K : Set G) ≃ H × K := sorry

open Matrix
def Matrix.center_of_GeneralLinearGroup_eq_scalar (n : ℕ) (K : Type*) [Field K] :
  K ≃ Subgroup.center (GeneralLinearGroup (Fin n) K) := sorry
