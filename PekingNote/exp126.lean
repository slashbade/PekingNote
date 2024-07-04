import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Fintype.Basic
-- import Mathlib.Algebra.Group.Subgroup.Finite
-- import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Subgroup.Center


open MulAction ConjClasses Fintype

variable (G : Type*) [Group G] [DecidableEq G]

/-- Conjugacy classes form a partition of G, stated in terms of cardinality. -/
theorem sum_conjClasses_card_eq_card [Fintype <| ConjClasses G] [Fintype G]
    [∀ x : ConjClasses G, Fintype x.carrier] :
    ∑ x : ConjClasses G, card x.carrier = card G := by
  suffices h_equiv : (Σ x : ConjClasses G, x.carrier) ≃ G by simpa using (card_congr h_equiv)
  simpa [carrier_eq_preimage_mk] using Equiv.sigmaFiberEquiv ConjClasses.mk

/-- The **class equation** for finite groups. The cardinality of a group is equal to the size
of its center plus the sum of the size of all its nontrivial conjugacy classes. -/
theorem Group.nat_card_center_add_sum_card_noncenter_eq_card' [Fintype G] [Fintype <| noncenter G]:
    card (Subgroup.center G) + ∑ x ∈ noncenter G, card x.carrier = card G := by
  nth_rw 2 [← sum_conjClasses_card_eq_card]
  rw [← Finset.sum_sdiff (ConjClasses.noncenter G).toFinset.subset_univ]; congr 1
  classical
  calc card (Subgroup.center G)
      /-This step requires classical-/
      = card ((noncenter G)ᶜ : Set (ConjClasses G)) := card_congr ((mk_bijOn G).equiv _)
    _ = Finset.card (Finset.univ \ (noncenter G).toFinset) := by
      rw [← Set.toFinset_card, Set.toFinset_compl, Finset.compl_eq_univ_sdiff]
    _ = ∑ x ∈ Finset.univ \ (noncenter G).toFinset, 1 := Finset.card_eq_sum_ones _
  rw [Finset.sum_congr _ _]; rfl
  rintro ⟨g⟩ hg
  rw [← Finset.compl_eq_univ_sdiff, ← Set.toFinset_compl, Set.mem_toFinset,
    Set.mem_compl_iff, mem_noncenter, Set.not_nontrivial_iff] at hg
  rw [← Set.toFinset_card, eq_comm, Finset.card_eq_one]
  constructor; swap; use g;
  rw [← Set.toFinset_singleton]
  exact Set.toFinset_congr (Set.Subsingleton.eq_singleton_of_mem hg mem_carrier_mk)
