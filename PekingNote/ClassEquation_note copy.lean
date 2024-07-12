import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.GroupAction.ConjAct
/-!
########################################################
  Group Actions, Conjugacy Classes, and Class Equation
########################################################

- Basic API of Group Actions
- Construct of Sum Type and lemmas
- Multiset.card and Finset.card, and card
- Summation of Finset
- Proof of Class Equation

-/

/-!
=======================
  Finset and Multiset
=======================

Some basic lemmas about Finset and Multiset are provided here.

-/

section MulAction

variable {G : Type} [Group G]

#check MulAction

/- Left Action by Group Multiplication -/
#synth SMul G G

instance : MulAction G G where
  one_smul := one_mul
  mul_smul := mul_assoc

/- Trivial Action on Group -/

/- Natural Action for Symmetric Group -/

/- Conjugacy Action for Group -/

end MulAction

section Conj

#check IsConj.setoid

end Conj

/-!
=======================
  Sigma Type in Lean
=======================

-/
section SigmaType

#check Sigma

/-! A basic equivalence for Sigma Type-/
def sigmaFiberEquiv' {α β : Type*} (f : α → β) : (Σ y : β, { x // f x = y }) ≃ α where
  toFun := fun ⟨b, a, ha⟩ => a
  invFun a := ⟨f a, a, rfl⟩
  left_inv := by
    rintro ⟨b, a, rfl⟩
    simp only [Sigma.mk.inj_iff]
  right_inv := by intro x; simp


namespace Finset

lemma sum_const' {α : Type*} (s : Finset α) (n : ℕ) : ∑ _x ∈ s, n = card s • n := sorry

lemma card_eq_sum_ones' {α : Type*} (s : Finset α) : card s = ∑ x ∈ s, 1 := sorry

end Finset

#check Sigma.instFintype
end SigmaType

section card

end card

/-!
===========================
  Proof of Class Equation
===========================

Class equation is stated as cardinality of a group is equal to the size of its center plus the sum of the size of all its nontrivial conjugacy classes.

.. default-role:: lean4

-/

/-! **Mathlib Version** of ``ClassEquation`` -/
#check Group.nat_card_center_add_sum_card_noncenter_eq_card

/-!
Class Equation theorem should be proved in the scope of ``Classical``. In this circumstance, every proposition is decidable. To avoid unnecessary coersion, we use ``Fintype.card`` to measure the size of a ``Fintype``.
-/
open ConjClasses Fintype Classical

#check Fintype.card

/-! **Statement** ``G`` is a ``Group`` -/
variable (G : Type*) [Group G]

/-!
Partition of Group by Conjugacy Classes
=======================================

Conjugacy classes form a partition of G, stated in terms of cardinality. -/
theorem sum_conjClasses_card_eq_card'  [Fintype G] :
    ∑ x : ConjClasses G, card x.carrier = card G := by
  suffices h_equiv : (Σ x : ConjClasses G, x.carrier) ≃ G by
  /- Rewrite the goal in terms of cardinality -/
    rw [← Fintype.card_sigma]
    exact card_congr h_equiv
  simp only [carrier_eq_preimage_mk]
  exact Equiv.sigmaFiberEquiv ConjClasses.mk
  -- simpa [carrier_eq_preimage_mk] using Equiv.sigmaFiberEquiv ConjClasses.mk

/-!
Class Equation for Finite Groups
================================

The cardinality of a group is equal to the size of its center plus the sum of the size of all its nontrivial conjugacy classes. -/
#check mk_bijOn
#check Set.toFinset_card
#check Set.toFinset_compl
#check Finset.compl_eq_univ_sdiff
theorem Group.nat_card_center_add_sum_card_noncenter_eq_card' [Fintype G]:
  card (Subgroup.center G) + ∑ x ∈ noncenter G, card x.carrier = card G := by
  /- Rewrite `G` as partitioned by its conjugacy classes -/
  nth_rw 2 [← sum_conjClasses_card_eq_card']
  /- Cancel out nontrivial conjugacy classes from summation -/
  rw [← Finset.sum_sdiff (ConjClasses.noncenter G).toFinset.subset_univ]; congr 1
  /- Now we can obtain the result by calculation -/
  calc
    _ = card ((noncenter G)ᶜ : Set (ConjClasses G)) := by
      exact card_congr (mk_bijOn G).equiv
    _ = Finset.card (Finset.univ \ (noncenter G).toFinset) := by
      rw [← Set.toFinset_card, Set.toFinset_compl, Finset.compl_eq_univ_sdiff]
    _ = ∑ x ∈ Finset.univ \ (noncenter G).toFinset, 1 := by
      exact Finset.card_eq_sum_ones' _
    _ = ∑ x ∈ Finset.univ \ (noncenter G).toFinset, card x.carrier := by sorry
