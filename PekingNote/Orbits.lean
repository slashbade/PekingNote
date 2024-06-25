import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.Coset
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Deprecated.Subgroup
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.Data.Nat.Factors

import PekingNote.Basic

open MulAction Classical
open scoped Pointwise
variable {G α : Type} [Group G] [MulAction G α]

#print MulAction.orbit

--def in mathlib
#print MulAction.IsPretransitive
-- def in note
def MulAction.IsTransitive (G α : Type) [Group G] [MulAction G α] := ∃ a : α, orbit G a = α

instance IsTrans.IsPretrans (h : IsTransitive G α) : IsPretransitive G α where
  exists_smul_eq := by
    intro x y
    simp [IsTransitive] at h
    obtain ⟨a,ha⟩ := h
    have hx : x ∈ ↑(orbit G a) := by
      have : α = @Set.univ α := sorry
      sorry
    have hy : y ∈orbit G a := sorry
    rw [MulAction.mem_orbit_iff] at hx hy
    obtain ⟨gx,hx⟩ := hx
    obtain ⟨gy,hy⟩ := hy
    use gy*gx⁻¹
    rw [←hx, ←mul_smul, mul_assoc]
    simp only [mul_left_inv, mul_one, hy]

lemma IsTrans_of_IsPretrans [IsPretransitive G α] : IsTransitive G α := sorry

/-! Example 1.14 -/

instance : SMul (Equiv.Perm (Fin n)) (Fin n) where
  smul := fun f x => f x

instance Sn.IsPretransitive : IsPretransitive (Equiv.Perm (Fin n)) (Fin n) where
  exists_smul_eq := by
    intro x y
    use Equiv.swap x y
    rw [Equiv.Perm.smul_def (Equiv.swap x y) x]
    simp only [Equiv.Perm.smul_def, Equiv.swap_apply_left]

-- unsolved! the conjugation action of S3 on itself has 3 orbits

/-! Example 1.15 -/
-- 1.15 (1)
#check MulAction.orbit.eq_or_disjoint
#check MulAction.IsPartition.of_orbits
#check MulAction.isBlock_orbit
--1.15 (2)
#check MulAction.ofQuotientStabilizer
#check MulAction.orbitEquivQuotientStabilizer
--1.15 (3)
#check MulAction.card_orbit_mul_card_stabilizer_eq_card_group
lemma card_orbit_dvd_group {a : α} : Nat.card (orbit G a) ∣ (Nat.card G) := by
  rw [Nat.card_congr (orbitEquivQuotientStabilizer G a)]
  apply Subgroup.card_quotient_dvd_card

/-! Example 1.16 -/
#check MulAction.card_eq_sum_card_group_div_card_stabilizer

/-! Example 1.17 -/
#check Subgroup.card_subgroup_dvd_card
#check Subgroup.card_quotient_dvd_card

/-! def 1.18 -/
#check Subgroup.index

/-! Example 1.19 -/

#synth AddGroup ℤ

def Int_even := {n : ℤ| Even n}

instance evenAddSubgroup : AddSubgroup ℤ where
  carrier := Int_even
  add_mem' := by simp [Int_even]; intros a b ha hb; exact Even.add ha hb
  zero_mem' := by simp [Int_even]
  neg_mem' := by simp [Int_even]

lemma even_index_eq_two : AddSubgroup.index evenAddSubgroup = 2 := by
  rw [AddSubgroup.index_eq_two_iff]
  use 1
  intro b
  rw [←xor_not_not]
  simp [xor_not_right,evenAddSubgroup,Int_even]
  refine Iff.symm ((fun {a b} => iff_not_comm.mp) ?h.a)
  exact @Int.even_add_one b

/-! Example 1.20 -/
namespace ConjAct
#check MulAction.isPretransitive_quotient
#check ConjAct.stabilizer_eq_centralizer

#synth MulAction (ConjAct G) G

lemma ofConjAct_eq {G : Type} {g h : G} [Group G] : ofConjAct g = ofConjAct h ↔ g = h := sorry

lemma stabilizer_eq_centralizer1 {G : Type} {g : G} [Group G] :
  stabilizer (ConjAct G) g = Subgroup.centralizer {ConjAct.toConjAct g} := by
    ext x
    simp only [mem_stabilizer_iff,Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [ConjAct.smul_def,←ofConjAct_inv, ←ConjAct.ofConjAct_toConjAct g,←ofConjAct_mul,←ofConjAct_mul]
    rw [ofConjAct_eq]
    simp only [ofConjAct_toConjAct]
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm

lemma stabilizer_univ_eq_center {G : Type} {g : G} [Group G] :
  MulAction.kernel (ConjAct G)  G  = Subgroup.center (ConjAct G) := by
    ext x
    rw [Subgroup.mem_center_iff,Kernel.mem_kernel_iff]
    simp_rw [ConjAct.smul_def]
    sorry

end ConjAct

#check Equiv.Perm.subgroupOfMulAction

lemma prime_factor_aux (nt : 1 < n) (hp : p = (n.factors).head (by
  simp only [ne_eq,Nat.factors_eq_nil, not_or]
  exact (Nat.two_le_iff n).mp nt)) : ∀ a : Nat, a ∣ n ∧ a ∣ p.factorial → a = p := sorry

lemma p_index_subgroup_normal  [Group G] [Fintype G] (nt : 1 < n) (h : Fintype.card G = n) (hnt : n.factors ≠ [] := by
  simp only [ne_eq,Nat.factors_eq_nil, not_or]
  exact (Nat.two_le_iff n).mp nt) (hp : p = (n.factors).head hnt) :
    ∀ H : Subgroup G, H.index = p → H.Normal := by
      intro H Hind
      let K := MulAction.kernel G (G⧸H)
      have ker := @Kernel.kernel_of_permHom (G⧸H) G _ _
      have iso := QuotientGroup.quotientKerEquivRange (MulAction.toPermHom G (G⧸H))
      have : G⧸K ≃* (toPermHom G (G ⧸ H)).range := by
        sorry
      have card_dvd : Fintype.card (G ⧸ K) ∣ Fintype.card (Equiv.Perm (G⧸H)) := by
        rw [Fintype.card_congr <| MulEquiv.toEquiv this]
        have := Subgroup.card_subgroup_dvd_card (MonoidHom.range <| toPermHom G (G⧸H))
        simp only [Nat.card_eq_fintype_card] at this
        assumption
      rw [Fintype.card_perm] at card_dvd
      have cardG := Subgroup.card_eq_card_quotient_mul_card_subgroup K
      rw [←Subgroup.index_eq_card H, Hind] at card_dvd
      repeat
        rw [Nat.card_eq_fintype_card] at cardG
      rw [h] at cardG
      have card_dvd' : Fintype.card (G ⧸ K) ∣ n := by simp only [cardG, dvd_mul_right]
      have cardGK := prime_factor_aux nt hp (Fintype.card (G ⧸ K)) ⟨card_dvd',card_dvd⟩
      rw [cardGK] at cardG
      have cardG' := Subgroup.index_mul_card H
      rw [Hind, h] at cardG'
      have : Fintype.card H = Fintype.card K := by
        rw [cardG] at cardG'
        exact Nat.mul_left_cancel (Nat.pos_of_mem_factors (hp ▸ (List.head_mem hnt) )) cardG'
      have KssH : ∀ g ∈ K, g ∈ H := by
        intro g memK
        have := Kernel.mem_kernel_iff.1 memK ⟦1⟧
        simp only at this
        sorry
      have KeqH : K = H := sorry
      rw [←KeqH]
      apply Kernel.MulAction.kernel.normal
