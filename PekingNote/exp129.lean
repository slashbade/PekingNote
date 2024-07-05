import Mathlib.Data.Fintype.Basic

import Mathlib.Algebra.Group.Conj
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Multiset.Basic

import Mathlib.GroupTheory.SpecificGroups.Cyclic

#check Nat.Partition

open Equiv.Perm
open Multiset

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev SymmGroup (n : ℕ) := Equiv.Perm <| Fin n

-- instance symm_group_group (n : ℕ) : Group (SymmGroup n) := @Equiv.Perm.permGroup (Fin n)

namespace Equiv.Perm

lemma orderOf_swap : ∀ (n : ℕ) (i j : Fin n), orderOf (Equiv.swap i j) <= 2 := by
  intros n i j
  exact orderOf_le_of_pow_eq_one (by decide)
    (by rw [pow_two, ext_iff]; intro x; rw [mul_apply (Equiv.swap i j) (Equiv.swap i j) x]; simp)


end Equiv.Perm



namespace SymmGroup

#check Equiv.Perm.cycleType_conj
#check isConj_of_cycleType_eq
#check isConj_iff_cycleType_eq
#check partition_eq_of_isConj
-- #check List.Mem.tail

variable {n : ℕ}

def toPerm (σ : SymmGroup n) : Equiv.Perm (Fin n) := σ

instance : Setoid (SymmGroup n) := IsConj.setoid (SymmGroup n)

instance : Fintype (SymmGroup n) := by infer_instance

instance : MulAction (SymmGroup n) (Fin n) where
  one_smul := one_apply
  mul_smul := mul_apply

def p1 : SymmGroup 3 := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩
def p2 : SymmGroup 3 := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩
def p12 : SymmGroup 5 := c[0, 4, 1]
def p21 : SymmGroup 4 := c[2, 1]

-- #eval p12 ∘ p21
#eval @decomposeFin 4 p12
#eval p12.partition.parts
#eval (@Finset.univ (SymmGroup 3) _).image fun σ => (ConjClasses.mk σ).unquot
#eval (@Finset.univ (SymmGroup 3) _).image fun σ => σ.partition.parts


def S3_not_cyclic : ¬ IsCyclic (SymmGroup 3) := by
  intro h
  rw [isCyclic_iff_exists_ofOrder_eq_natCard] at h
  have symm3_card : Nat.card (SymmGroup 3) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
  contrapose! h
  intro σ
  rw [symm3_card]
  fin_cases σ
  . simp
  . simp;
    have : orderOf (@Equiv.swap (Fin 3) _ 1 2) <= 2 := by
      exact orderOf_swap 3 (Fin.mk 1 (by simp)) (Fin.mk 2 (by simp))
    linarith
  . simp; sorry
  . simp; sorry
  . simp; sorry
  . simp; sorry

/- Generalized version -/
def Fin_of_Fin_succ_stablizer : MulAction.stabilizer (SymmGroup n.succ) (0 : Fin n.succ) ≃ SymmGroup n where
  toFun s := (decomposeFin s.1).2
  invFun σ := ⟨decomposeFin.symm (0, σ),
    by rw [MulAction.mem_stabilizer_iff]; simp;⟩
  left_inv s := by
    have : (decomposeFin s.1).1 = 0 := by
      simp [decomposeFin]; let h := s.2; rw [MulAction.mem_stabilizer_iff] at h; exact h
    simp_rw [← this, Prod.eta, Equiv.symm_apply_apply]
  right_inv σ := by simp_rw [Equiv.apply_symm_apply]

/- Example 1.12(2) -/
def S4_stablizer_eq_S3 : MulAction.stabilizer (SymmGroup 4) (0 : Fin 4) ≃ SymmGroup 3 :=
  Fin_of_Fin_succ_stablizer

/- Computational verification -/
#eval @Finset.univ (MulAction.stabilizer (SymmGroup 4) (0 : Fin 4)).carrier _
#eval @Finset.univ (SymmGroup 3) _

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

namespace Multiset

lemma cons_toList {α : Type*} (a : α) (l : Multiset α) : (a ::ₘ l).toList = a :: l.toList := by
  simp [Multiset.cons, Multiset.toList]; sorry
end Multiset

variable {n : ℕ} {hn2 : 2 ≤ n}

/-This is an aux fcn so so that the ones are filtered-/
def cananical_perm_of_parts (parts : List ℕ) (cann : List (Fin n)) : SymmGroup n :=
  match parts with
  | [] => 1
  | ph :: pt => (cann.take ph).formPerm * (cananical_perm_of_parts pt (cann.drop ph))

lemma add_eq_of_cananical_perm (p q : List ℕ) :
  cananical_perm_of_parts (p ++ q) (List.finRange n) =
  cananical_perm_of_parts p (List.finRange n) * cananical_perm_of_parts q (List.finRange n) := by
  sorry

lemma eq_of_cananical_perm (p : List ℕ) (cann1 cann2 : List (Fin n))
(h : cann1.length >= p.length ∧ cann2.length >= p.length) :
cananical_perm_of_parts p cann1 = cananical_perm_of_parts p cann2
:= sorry

-- lemma cycleType_eq_of_cananical_perm {n : ℕ} (σ : SymmGroup n) : σ.cycleType

noncomputable def conjClasses_of_partition (p : Nat.Partition n) : ConjClasses (SymmGroup n) := by
  let parts := p.parts.filter (· >= 2)
  exact ⟦cananical_perm_of_parts parts.toList (List.finRange n)⟧

/- This function construct a partition with one s-/
noncomputable def partition_of_conjClasses (c : ConjClasses (SymmGroup n)) : Nat.Partition n :=
  c.out.partition

noncomputable def symmetry_group_ConjClasses_equiv_partition :
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
      have take_nodup: (List.take σ.support.card (List.finRange n)).Nodup := by
        suffices h : (List.finRange n).Nodup by exact List.Nodup.sublist (List.take_sublist _ _) h
        exact List.nodup_finRange n
      rw [cycleType_def, Multiset.map_eq_singleton]; use (List.take σ.support.card (List.finRange n)).formPerm
      constructor
      . rw [Finset.val_eq_singleton_iff, cycleFactorsFinset_eq_singleton_iff]
        constructor; swap; rfl;
        apply List.isCycle_formPerm (take_nodup);
        simp only [List.length_take, List.length_finRange]
        exact le_min (one_lt_card_support_of_ne_one hσ.ne_one) (hn2)
      simp only [Function.comp_apply]
      rw [List.support_formPerm_of_nodup ((List.finRange n).take σ.support.card) take_nodup ?_, List.toFinset_card_of_nodup take_nodup]
      . simp only [List.length_take, List.length_finRange, min_eq_left_iff, ge_iff_le, SymmGroup.card_support_le_card]
      by_contra! h
      rw [← List.length_eq_one, List.length_take, List.length_finRange] at h
      have hhh := IsCycle.two_le_card_support hσ
      rw [min_eq_left_iff.mpr SymmGroup.card_support_le_card] at h
      linarith
    rw [Disjoint.cycleType]; nth_rw 2 [IsCycle.cycleType];
    simp only [coe_singleton, singleton_add, cons_toList, cananical_perm_of_parts];
    have cann_disj : Disjoint ((List.finRange n).take σ.support.card).formPerm
      (cananical_perm_of_parts τ.cycleType.toList ((List.finRange n).drop σ.support.card)) := by sorry
    have : ((List.finRange n).take σ.support.card).formPerm.cycleType = σ.cycleType := by sorry
    rw [Disjoint.cycleType cann_disj, this]
    congr 1;
    nth_rw 2 [←h2]; rw [eq_of_cananical_perm τ.cycleType.toList _ _]; sorry
    exact hc; exact hd
  right_inv := sorry
