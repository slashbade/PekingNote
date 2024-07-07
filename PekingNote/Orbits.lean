import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.Coset
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Deprecated.Subgroup
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.PrimeFin

open MulAction Classical
open scoped Pointwise
variable {G α : Type} [Group G] [MulAction G α]


variable {A : Type} [MulAction G A]
#check MulAction.stabilizer

section Aux
lemma Subgroup.subset_of_le [Group G] {H K : Subgroup G} : H ≤ K → H.carrier ⊆ K.carrier :=
  fun h => (fun _ hx => h hx)

lemma Subgroup.card_le_card [Group G] {H K : Subgroup G} [Fintype H] [Fintype K] (le : H ≤ K) :
  Fintype.card H ≤ Fintype.card K := by
    have : H.carrier ⊆ K.carrier := fun x hx => le hx
    exact Set.card_le_card this

lemma prime_factor_aux (nt : 1 < n) (hp : p = (n.factors).head (by
  simp only [ne_eq,Nat.factors_eq_nil, not_or]
  exact (Nat.two_le_iff n).mp nt)) : ∀ a : Nat, a ∣ n ∧ a ∣ p.factorial  → a = p ∨ a = 1:= by
    intro a ha
    have h1 := Nat.primeFactors_mono ha.1 sorry
    have h2 : ∀ q ∈ a.primeFactors, p ≤ q := fun q hq => (by have := h1 hq; sorry)
    sorry

end Aux

def setStabilizer (s : Set A) : Subgroup G := sInf (Set.range (fun a:s => (MulAction.stabilizer G a.1)))

def MulAction.kernel (G A : Type) [Group G] [MulAction G A] : Subgroup G := setStabilizer (@Set.univ A)

/-! Example 1.9 -/
namespace Kernel

lemma mem_kernel_iff {x : G} {A : Type} [MulAction G A] : x ∈ MulAction.kernel G A ↔ ∀ a : A, x • a = a := by
  constructor
  · intro h a
    simp [MulAction.kernel,Set.mem_range,setStabilizer] at h
    exact h a
  · intro h
    simp only [MulAction.kernel,setStabilizer]
    simp only [Subgroup.mem_sInf, Set.mem_range, Subtype.exists, Set.mem_univ, exists_const,
      forall_exists_index, forall_apply_eq_imp_iff, MulAction.mem_stabilizer_iff]
    assumption

lemma kernel_of_permHom : MonoidHom.ker (MulAction.toPermHom G A) = MulAction.kernel G A := by
  ext x
  rw [MonoidHom.mem_ker,mem_kernel_iff]
  constructor
  · simp
    intro h a
    rw [←MulAction.toPerm_apply x a,h]
    rfl
  · simp only [MulAction.toPermHom_apply]
    intro h
    ext y
    simp only [MulAction.toPerm_apply]
    exact h y

instance : (MulAction.kernel G A).Normal := by
  rw [←kernel_of_permHom]
  exact MonoidHom.normal_ker (MulAction.toPermHom G A)

noncomputable def quotient_equiv : G ⧸ (MulAction.kernel G A) ≃ (toPermHom G A).range := by
  have := QuotientGroup.quotientKerEquivRange (MulAction.toPermHom G A)
  exact ((Subgroup.quotientEquivOfEq (@kernel_of_permHom G _ A _) ).symm).trans (this.toEquiv)

end Kernel

#check MulAction.stabilizer_quotient
lemma quotient_action_kernel_le [Group G] (H : Subgroup G): MulAction.kernel G (G ⧸ H) ≤ H := by
  intro x h
  rw [Kernel.mem_kernel_iff] at h
  exact MulAction.stabilizer_quotient H ▸ (MulAction.mem_stabilizer_iff.2 <| h (1 : G))


lemma eq_of_le_of_card_eq [Group G] {K H : Subgroup G} [Fintype K] [Fintype H] (le : K ≤ H)
  (card_eq : Fintype.card K = Fintype.card H) : K = H := by
    have KssH : K.carrier ⊆ H.carrier := fun x hx => le hx
    have := Finset.eq_of_subset_of_card_le (Set.toFinset_subset_toFinset.2 KssH)
    simp only [Set.toFinset_card, Set.toFinset_inj] at this
    have carrier_eq := this <| le_of_eq card_eq.symm
    ext x
    simp_rw [←Subgroup.mem_carrier,carrier_eq]

#print MulAction.orbit

--def in mathlib
#print MulAction.IsPretransitive
-- def in note
def MulAction.IsTransitive (G α : Type) [Group G] [MulAction G α] := ∃ a : α, orbit G a = Set.univ

instance IsTrans.IsPretrans (h : IsTransitive G α) : IsPretransitive G α where
  exists_smul_eq := by
    intro x y
    simp [IsTransitive] at h
    obtain ⟨a,ha⟩ := h
    have hx : x ∈ orbit G a := (eq_comm.1 ha) ▸ (Set.mem_univ x)
    have hy : y ∈orbit G a := (eq_comm.1 ha) ▸ (Set.mem_univ x)
    rw [MulAction.mem_orbit_iff] at hx hy
    obtain ⟨gx,hx⟩ := hx
    obtain ⟨gy,hy⟩ := hy
    use gy*gx⁻¹
    rw [←hx, ←mul_smul, mul_assoc]
    simp only [mul_left_inv, mul_one, hy]

lemma IsTrans_of_IsPretrans [h : IsPretransitive G α] [hne : Nonempty α]: IsTransitive G α := by
  have := h.exists_smul_eq
  simp [IsTransitive]
  rcases hne with ⟨x⟩
  have := this x
  use x
  ext y
  constructor
  · intro; simp
  · intro; exact MulAction.mem_orbit_iff.2 (this y)

/-! Example 1.14 -/

variable {n:Nat}
#synth MulAction (Equiv.Perm (Fin n)) (Fin n)

instance Sn.IsPretransitive : IsPretransitive (Equiv.Perm (Fin n)) (Fin n) where
  exists_smul_eq := by
    intro x y
    use Equiv.swap x y
    rw [Equiv.Perm.smul_def (Equiv.swap x y) x]
    simp only [Equiv.Perm.smul_def, Equiv.swap_apply_left]

/-! Example 1.15 -/
-- 1.15 (1)
#check MulAction.orbit.eq_or_disjoint
#check MulAction.IsPartition.of_orbits
--1.15 (2)
#check MulAction.ofQuotientStabilizer
#check MulAction.orbitEquivQuotientStabilizer
--1.15 (3)
#check MulAction.card_orbit_mul_card_stabilizer_eq_card_group
#check QuotientGroup.leftRel
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
#check ZMod 2
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

lemma ofConjAct_eq {G : Type} {g h : G} [Group G] : ofConjAct g = ofConjAct h ↔ g = h :=
  @Equiv.apply_eq_iff_eq (ConjAct G) G (@ofConjAct G _) g h

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
#check Set.smulSet

    -- let q := Classical.choice <| Finset.Nonempty.to_subtype <| Nat.nonempty_primeFactors.2
    -- have hq := h2 q q.2
    -- by_cases hqq : p = q
    -- · sorry
    -- · sorry

lemma p_index_subgroup_normal  [Group G] [Fintype G] (nt : 1 < n) (h : Fintype.card G = n)
  (hnt : n.factors ≠ [] := by
  simp only [ne_eq,Nat.factors_eq_nil, not_or]
  exact (Nat.two_le_iff n).mp nt) (hp : p = (n.factors).head hnt) :
    ∀ H : Subgroup G, H.index = p → H.Normal := by
      intro H Hind
      let K := MulAction.kernel G (G⧸H)
      have : G⧸K ≃ (toPermHom G (G ⧸ H)).range := Kernel.quotient_equiv
      have card_dvd : Fintype.card (G ⧸ K) ∣ Fintype.card (Equiv.Perm (G⧸H)) := by
        rw [Fintype.card_congr <| this]
        have := Subgroup.card_subgroup_dvd_card (MonoidHom.range <| toPermHom G (G⧸H))
        simp only [Nat.card_eq_fintype_card] at this
        assumption
      have cardG := Subgroup.card_eq_card_quotient_mul_card_subgroup K
      rw [Fintype.card_perm,←Subgroup.index_eq_card H, Hind] at card_dvd
      repeat
        rw [Nat.card_eq_fintype_card] at cardG
      rw [h] at cardG
      have card_dvd' : Fintype.card (G ⧸ K) ∣ n := by simp only [cardG, dvd_mul_right]
      have cardGK := prime_factor_aux nt hp (Fintype.card (G ⧸ K)) ⟨card_dvd',card_dvd⟩
      cases cardGK with
      | inl hl =>
        rw [hl] at cardG
        have cardG' := Subgroup.index_mul_card H
        rw [Hind, h] at cardG'
        have : Fintype.card H = Fintype.card K := by
          rw [cardG] at cardG'
          exact Nat.mul_left_cancel (Nat.pos_of_mem_factors (hp ▸ (List.head_mem hnt) )) cardG'
        exact (eq_of_le_of_card_eq (quotient_action_kernel_le H) this.symm) ▸ Kernel.instNormalKernel
      | inr hr =>
        rw [hr, one_mul] at cardG
        have cardG_le := le_of_eq_of_le cardG (Subgroup.card_le_card <| quotient_action_kernel_le H)
        rw [←h, ←Nat.card_eq_fintype_card, ←Nat.card_eq_fintype_card] at cardG_le
        exact (Subgroup.eq_top_of_le_card H cardG_le).symm ▸ (Subgroup.Normal.mk <| (fun _ _ => by simp))
