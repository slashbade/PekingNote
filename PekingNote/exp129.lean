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

end SymmGroup

/-This is an aux so so that the ones are filtered-/
def cananical_perm_of_parts (n : ℕ) (parts : List ℕ) : SymmGroup n :=
  match parts with
  | [] => 1
  | ph :: pt => ((Fin.list n).take ph).formPerm * (cananical_perm_of_parts n pt)

noncomputable def conjClasses_of_partition (n : ℕ) (p : Nat.Partition n) : ConjClasses (SymmGroup n) := by
  let parts := p.parts.filter (· >= 2)
  exact ⟦cananical_perm_of_parts n parts.toList⟧

/- This function construct a partition with one s-/
noncomputable def partition_of_conjClasses (n : ℕ) (c : ConjClasses (SymmGroup n)) : Nat.Partition n := by
  -- rw [← Fintype.card_fin n]
  exact (@Quotient.out (SymmGroup n) (IsConj.setoid (SymmGroup n)) c).partition

-- #check Function.Bijective

-- lemma symmetry_group_ConjClasses_equiv_partition' (n : ℕ) : ∃ f : (ConjClasses (SymmGroup n)) → n.Partition,
--   Function.Bijective f := by
--   constructor; swap;
--   intro c;
--   let g := @Quotient.out (SymmGroup n) (IsConj.setoid (SymmGroup n)) c
--   rw [← Fintype.card_fin n]
--   exact g.partition
--   . constructor
--     intro c1 c2 fh; sorry;

noncomputable def symmetry_group_ConjClasses_equiv_partition (n : ℕ) :
  (ConjClasses (SymmGroup n)) ≃ Nat.Partition n where
  toFun := partition_of_conjClasses n
  invFun := conjClasses_of_partition n
  left_inv := by
    intro c
    simp [partition_of_conjClasses, conjClasses_of_partition, SymmGroup.filter_parts_partition_eq_cycleType]
    sorry

  right_inv := sorry
