import Mathlib.Algebra.Group.Conj
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Multiset.Basic


#check Nat.Partition

open Equiv.Perm
open Multiset

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev SymmGroup (n : ℕ) := Equiv.Perm <| Fin n

-- instance symm_group_group (n : ℕ) : Group (SymmGroup n) := @Equiv.Perm.permGroup (Fin n)

namespace Equiv.Perm

end Equiv.Perm



namespace SymmGroup

#check Equiv.Perm.cycleType_conj
#check isConj_of_cycleType_eq
#check isConj_iff_cycleType_eq
#check partition_eq_of_isConj
#check List.Mem.tail

variable {n : ℕ}

def toPerm (σ : SymmGroup n) : Equiv.Perm (Fin n) := σ

instance : Setoid (SymmGroup n) := IsConj.setoid (SymmGroup n)

def partition (σ : SymmGroup n) : n.Partition where
  parts := σ.cycleType + Multiset.replicate (Fintype.card (Fin n) - σ.support.card) 1
  parts_pos {n hn} := by
    cases' mem_add.mp hn with hn hn
    · exact zero_lt_one.trans (one_lt_of_mem_cycleType hn)
    · exact lt_of_lt_of_le zero_lt_one (ge_of_eq (Multiset.eq_of_mem_replicate hn))
  parts_sum := by
    rw [sum_add, sum_cycleType, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one,
      add_tsub_cancel_of_le σ.support.card_le_univ, Fintype.card_fin]

theorem parts_partition {σ : SymmGroup n} :
    σ.partition.parts = σ.cycleType + Multiset.replicate (Fintype.card (Fin n) - σ.support.card) 1 :=
  rfl

theorem filter_parts_partition_eq_cycleType {σ : SymmGroup n} :
    ((partition σ).parts.filter fun n => 2 ≤ n) = σ.cycleType := by
  rw [parts_partition, filter_add, Multiset.filter_eq_self.2 fun _ => two_le_of_mem_cycleType,
    Multiset.filter_eq_nil.2 fun a h => ?_, add_zero]
  rw [Multiset.eq_of_mem_replicate h]
  decide

lemma card_support_le_card {σ : SymmGroup n} : σ.support.card ≤ n := by
  suffices h : σ.support.card ≤ Fintype.card (Fin n) by rw [Fintype.card_fin n] at h; exact h
  exact σ.support.card_le_univ

end SymmGroup

/-This is an aux so so that the ones are filtered-/
def cananical_perm_of_parts {n : ℕ} (parts : List ℕ) (cann : List (Fin n)) : SymmGroup n :=
  match parts with
  | [] => 1
  | ph :: pt => (cann.take ph).formPerm * (cananical_perm_of_parts pt (cann.drop ph))

noncomputable def cananical_perm_of_parts' {n : ℕ} (parts : Multiset ℕ) (cann : List (Fin n)) : SymmGroup n :=
  sorry

lemma add_eq_of_cananical_perm {n : ℕ} (p q : List ℕ) :
cananical_perm_of_parts (p ++ q) (List.finRange n) =
  cananical_perm_of_parts p (List.finRange n) * cananical_perm_of_parts q (List.finRange n) := by
  sorry

-- lemma cycleType_eq_of_cananical_perm {n : ℕ} (σ : SymmGroup n) : σ.cycleType

noncomputable def conjClasses_of_partition {n : ℕ} (p : Nat.Partition n) : ConjClasses (SymmGroup n) := by
  let parts := p.parts.filter (· >= 2)
  exact ⟦cananical_perm_of_parts parts.toList (List.finRange n)⟧

/- This function construct a partition with one s-/
noncomputable def partition_of_conjClasses {n : ℕ} (c : ConjClasses (SymmGroup n)) : Nat.Partition n :=
  c.out.partition

noncomputable def symmetry_group_ConjClasses_equiv_partition {n : ℕ} :
  (ConjClasses (SymmGroup n)) ≃ Nat.Partition n where
  toFun := partition_of_conjClasses
  invFun := conjClasses_of_partition
  left_inv := by
    intro c
    simp [partition_of_conjClasses, conjClasses_of_partition, SymmGroup.filter_parts_partition_eq_cycleType]
    suffices h : IsConj (cananical_perm_of_parts c.out.cycleType.toList (List.finRange n)) c.out by
      rw [←ConjClasses.mk_eq_mk_iff_isConj, ConjClasses.mk, ConjClasses.mk, Quotient.out_eq] at h; exact h
    rw [isConj_iff_cycleType_eq]
    induction' (c.out) using cycle_induction_on with σ hσ σ τ hd hc h1 h2
    . simp [cananical_perm_of_parts]
    . simp only [IsCycle.cycleType hσ, coe_singleton, toList_singleton, cananical_perm_of_parts, mul_one]
      rw [cycleType_def, Multiset.map_eq_singleton]; use (List.take σ.support.card (List.finRange n)).formPerm
      constructor
      . rw [Finset.val_eq_singleton_iff, cycleFactorsFinset_eq_singleton_iff]
        constructor; swap; rfl;
        sorry
      simp only [Function.comp_apply]
      have : (List.take σ.support.card (List.finRange n)).Nodup := by
        suffices h : (List.finRange n).Nodup by exact List.Nodup.sublist (List.take_sublist _ _) h
        exact List.nodup_finRange n
      rw [List.support_formPerm_of_nodup ((List.finRange n).take σ.support.card) this ?_, List.toFinset_card_of_nodup this]
      . simp only [List.length_take, List.length_finRange, min_eq_left_iff, ge_iff_le, SymmGroup.card_support_le_card]
      by_contra! h
      rw [← List.length_eq_one, List.length_take, List.length_finRange] at h
      have hhh := IsCycle.two_le_card_support hσ
      rw [min_eq_left_iff.mpr SymmGroup.card_support_le_card] at h
      linarith
    rw [Disjoint.cycleType]; nth_rw 2 [IsCycle.cycleType];
    simp only [coe_singleton, singleton_add, ];
    sorry; exact hc;exact hd
  right_inv := sorry
