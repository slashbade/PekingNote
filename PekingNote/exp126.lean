import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.ClassEquation
/-!
##################################
  From List to Conjugacy Classes
##################################

- Construction of List, Monoid Property
- Construct of Quotients Type, Sum Type
- From List to Multiset and Finset
- Summation of Finset

-/

/-!
=======================
  Finset and Multiset
=======================

Some basic lemmas about Finset and Multiset are provided here.

-/

section sumType

-- def sigmaFiberEquiv' {α β : Type*} (f : α → β) : (Σ y : β, { x // f x = y }) ≃ α where
  -- toFun a := a.2
  -- invFun b := ⟨⟩

end sumType


namespace Finset

lemma sum_const' {α : Type*} (s : Finset α) (n : ℕ) : ∑ _x ∈ s, n = card s • n := by
  rw [← Multiset.sum_replicate s.card n, Finset.card_def, ← s.val.map_const n]; congr;

lemma card_eq_sum_ones' {α : Type*} (s : Finset α) : card s = ∑ x ∈ s, 1 := by
  simp only [sum_const, smul_eq_mul, mul_one]

end Finset

/-!
===========================
  Proof of Class Equation
===========================

This file contains the proof of the class equation for finite groups. Class equation is stated as cardinality of a group is equal to the size of its center plus the sum of the size of all its nontrivial conjugacy classes.

Class equation itself has been proved in Mathlib. However, the proof touched with too many `simp` lemmas, and the proof is not easy to understand. This file provides a new proof of the class equation, which is more readable and understandable.

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
  /- To prove the lemma, it suffices to show that conjugacy classes do form a partition of G -/
  suffices h_equiv : (Σ x : ConjClasses G, x.carrier) ≃ G by
    simpa using (card_congr h_equiv)
  /- The proof of the equivalence is based on the bijection between the carrier of a conjugacy class and the conjugacy class itself -/
  simp only [carrier_eq_preimage_mk]
  exact Equiv.sigmaFiberEquiv ConjClasses.mk
  -- simpa [carrier_eq_preimage_mk] using Equiv.sigmaFiberEquiv ConjClasses.mk

/-!
Class Equation for Finite Groups
================================

The cardinality of a group is equal to the size of its center plus the sum of the size of all its nontrivial conjugacy classes. -/
theorem Group.nat_card_center_add_sum_card_noncenter_eq_card' [Fintype G]:
  card (Subgroup.center G) + ∑ x ∈ noncenter G, card x.carrier = card G := by
  /- Rewrite `G` as partitioned by its conjugacy classes -/
  nth_rw 2 [← sum_conjClasses_card_eq_card']
  /- Cancel out nontrivial conjugacy classes from summation -/
  rw [← Finset.sum_sdiff (ConjClasses.noncenter G).toFinset.subset_univ]; congr 1
  /- Now we can obtain the result by calculation -/
  calc card (Subgroup.center G) = card ((noncenter G)ᶜ : Set (ConjClasses G)) :=
    card_congr ((mk_bijOn G).equiv _)
    _ = Finset.card (Finset.univ \ (noncenter G).toFinset) := by
      rw [← Set.toFinset_card, Set.toFinset_compl, Finset.compl_eq_univ_sdiff]
    _ = ∑ x ∈ Finset.univ \ (noncenter G).toFinset, 1 :=
      Finset.card_eq_sum_ones _
    _ = ∑ x ∈ Finset.univ \ (noncenter G).toFinset, card x.carrier := by
      rw [Finset.sum_congr rfl _];
      rintro ⟨g⟩ hg; simp at hg
      rw [← Set.toFinset_card, eq_comm, Finset.card_eq_one]
      exact ⟨g, by rw [← Set.toFinset_singleton]; exact Set.toFinset_congr (Set.Subsingleton.eq_singleton_of_mem hg mem_carrier_mk)⟩
