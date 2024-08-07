import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!

============================
  Notes for Symmetry Group
============================

-/

/-!
Quotient Type
-------------
A typical idea to construct new map.
Example: Coset, ℤ/nℤ, ConjClasses, G-orbit etc.

-/
namespace Quotient

variable (G : Type*) (X : Type*) [Group G] [MulAction G X]

def orbit_setoid : Setoid X where
  r := fun x y => ∃ g : G, g • x = y
  iseqv := by
    constructor
    . intro x; exact ⟨1, MulAction.one_smul _⟩
    . intro x y hxy; rcases hxy with ⟨g, hg⟩; use g⁻¹; rw [←hg]; simp;
    intro x y z hxy hyz;
    rcases hxy with ⟨g, hg⟩
    rcases hyz with ⟨h, hh⟩
    exact ⟨h * g, by rw [mul_smul, ← hh, ← hg]⟩

def orbit_coset := Quotient (orbit_setoid G X: Setoid X)

end Quotient

/-!

Lean's Characterization of Finiteness
-------------------------------------

1. Decidability and Representation
2. List -> Multiset -> Finset

-/
namespace List

#check List

def l1 : List ℕ := [2, 5, 3, 3, 5, 8, 11]
def l2 : List ℕ := [5, 2, 3, 3, 5, 8, 11]

#check Multiset

#eval Multiset.ofList l1 = Multiset.ofList l2

#check Finset


-- structure MyPartition (n : ℕ) where
--   parts := Multiset ℕ
--   parts_pos := ∀ p ∈ parts, 0 < p

#eval l1



end List



/-!
Symmetry Group by Equivalence
-----------------------------
-/
def MySymmGroup (n : ℕ) := Equiv (Fin n) (Fin n)

namespace MySymmGroup

variable {n : ℕ}

end MySymmGroup


open Equiv.Perm
abbrev SymmGroup (n : ℕ) := Equiv.Perm <| Fin n
variable {n : ℕ}

def toPerm (σ : SymmGroup n) : Equiv.Perm (Fin n) := σ

instance : Setoid (SymmGroup n) := IsConj.setoid (SymmGroup n)

instance : Fintype (SymmGroup n) := inferInstance

instance : MulAction (SymmGroup n) (Fin n) where
  one_smul := Equiv.Perm.one_apply
  mul_smul := Equiv.Perm.mul_apply

/-!
Repr of Symmetry Group
----------------------
Cycle Notation
-/
namespace ConcreteSymmGroup

#check repr_perm
#check Fintype.decidableEqEquivFintype

end ConcreteSymmGroup

/-! Small Lemma -/
lemma Equiv.Perm.orderOf_swap : ∀ (n : ℕ) (i j : Fin n), orderOf (Equiv.swap i j) <= 2 := by
  intros n i j
  exact orderOf_le_of_pow_eq_one (by decide)
    (by rw [pow_two, ext_iff]; intro x; rw [mul_apply (Equiv.swap i j) (Equiv.swap i j) x]; simp)

/-!
Exercises for Symmetry Groups
-----------------------------
-/
namespace Exercise

/- Example 1.33(2) A Demonstration for case-by-case proof -/
lemma S3_not_cyclic : ¬ IsCyclic (SymmGroup 3) := by
  intro h
  let h_comm := h.commGroup
  let x1 : SymmGroup 3 := c[0, 1]
  let x2 : SymmGroup 3 := c[1, 2]
  have h_eq : x1 * x2 = x2 * x1 := mul_comm x1 x2
  have h_ne : x1 * x2 ≠ x2 * x1 := by unfold_let; decide
  exact h_ne h_eq

/- Example 1.12(2) Generalized version -/
def Fin_of_Fin_succ_stablizer : MulAction.stabilizer (SymmGroup n.succ) (0 : Fin n.succ) ≃ SymmGroup n where
  toFun s := (decomposeFin s.1).2
  invFun σ := ⟨decomposeFin.symm (0, σ),
    by rw [MulAction.mem_stabilizer_iff]; simp;⟩
  left_inv s := by
    have : (decomposeFin s.1).1 = 0 := by
      simp [decomposeFin]; let h := s.2; rw [MulAction.mem_stabilizer_iff] at h; exact h
    simp_rw [← this, Prod.eta, Equiv.symm_apply_apply]
  right_inv σ := by simp_rw [Equiv.apply_symm_apply]

/- Example 1.12(2) Proof by generalizarion-/
def S4_stablizer_eq_S3 : MulAction.stabilizer (SymmGroup 4) (0 : Fin 4) ≃
  SymmGroup 3 :=
  sorry


end Exercise

/-!
Induction Techniques for Symmetry Groups
-/
namespace CycleInduction

open Equiv
variable {α : Type*} [Fintype α] [DecidableEq α]

#check Perm.cycle_induction_on
#check Perm.IsCycle.conj
#check Perm.Disjoint.conj
#check Perm.Disjoint.cycleType
#check Perm.Disjoint.card_support_mul

theorem cycleType_conj {σ τ : Perm α} : (τ * σ * τ⁻¹).cycleType = σ.cycleType := sorry

theorem cycleType_sum {σ : Perm α} : σ.cycleType.sum = σ.support.card := sorry

end CycleInduction

/-!
Correspondence between Conjugacy Classes and Partitions
-------------------------------------------------------
-/
section ConjPartition

#check Equiv.Perm.cycleType_conj
#check isConj_of_cycleType_eq
#check isConj_iff_cycleType_eq
#check partition_eq_of_isConj

lemma bij_conjClasses_partition : ∃ f : ConjClasses (SymmGroup n) → n.Partition, Function.Bijective f := sorry

end ConjPartition
