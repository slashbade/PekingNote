import Mathlib.Algebra.Group.Conj
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Multiset.Basic


#check Nat.Partition

open Equiv.Perm

abbrev SymmGroup (n : ℕ) := Equiv.Perm <| Fin n

instance symm_group_group (n : ℕ) : Group (SymmGroup n) := @Equiv.Perm.permGroup (Fin n)

namespace Equiv.Perm

end Equiv.Perm



namespace SymmGroup

#check Equiv.Perm.cycleType_conj
#check isConj_of_cycleType_eq
#check isConj_iff_cycleType_eq
#check partition_eq_of_isConj
#check List.Mem.tail

end SymmGroup

def cananical_perm_of_partition (n : ℕ) (parts : List ℕ) : SymmGroup n :=
  match parts with
  | [] => 1
  | ph :: pt => ((Fin.list n).take ph).formPerm * (cananical_perm_of_partition n pt)



def partition_of_conjClasses (n : ℕ) (c : ConjClasses (SymmGroup n)) : Nat.Partition n := by
  -- intro c
  -- have : n = Fintype.card (Fin n) := Eq.symm (Fintype.card_fin n)
  -- rw [this]
  -- exact (@Quotient.out (SymmGroup n) (IsConj.setoid (SymmGroup n)) c).partition
  sorry

lemma p_eq (n : ℕ) (parts : List ℕ) : (cananical_perm_of_partition n parts).partition.parts.toList = parts := by
  induction parts
  . simp [cananical_perm_of_partition, partition];
    sorry
  sorry

-- #check Function.Bijective

lemma symmetry_group_ConjClasses_equiv_partition' (n : ℕ) : ∃ f : (ConjClasses (SymmGroup n)) → n.Partition, Function.Bijective f :=
  sorry

def symmetry_group_ConjClasses_equiv_partition (n : ℕ) : (ConjClasses (SymmGroup n)) ≃ Nat.Partition n where
  toFun := by
    intro c
    let f := @Quotient.out (SymmGroup n) (IsConj.setoid (SymmGroup n)) c
    have : Fintype.card (Fin n) = n := by simp only [Fintype.card_fin]
    rw [← this]
    -- exact f.partition
    sorry
  invFun := by
    intro p
    -- exact ⟦cananical_perm_of_partition n p.parts.toList⟧
    sorry
  left_inv := by
    intro c;
    sorry
  right_inv := sorry
