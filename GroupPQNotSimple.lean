import Mathlib.GroupTheory.Sylow

#check Sylow.unique_of_normal
#check card_sylow_dvd_index
#check card_sylow_modEq_one

open Classical

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (pp : Nat.Prime p) ( pq : Nat.Prime q)

variable {G : Type} [Group G] [Fintype G] [Fintype (Sylow p G)]

theorem Sylow.normal_of_unique {P : Sylow p G} (h : Unique (Sylow p G)) : P.Normal := by
  constructor
  intro n ninP g
  let Q := g • P
  have h1: Q = h.default := h.uniq Q
  have h2: P = h.default := h.uniq P
  have : P=Q :=by rw [h1, ←h2]
  rw [this]
  dsimp [Q]
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  simpa

lemma not_simple_of : (∃ H : Subgroup G, H.Normal ∧ H ≠ ⊤ ∧ H ≠ ⊥) → ¬IsSimpleGroup G:= by
  intro h
  contrapose! h
  intro H HN h
  have := Subgroup.Normal.eq_bot_or_eq_top HN
  tauto

namespace Orderpq
variable (hG : Fintype.card G = p * q) {P : Sylow p G} {Q : Sylow p G} (qltp : q < p)

lemma cardP (pp : Nat.Prime p) ( pq : Nat.Prime q) (P : Sylow p G): Fintype.card P = p := by
  have hdvd : (Nat.factorization (Fintype.card G)) p = 1 := by
    rw [hG, Nat.factorization_mul (Nat.ne_of_gt <| Nat.Prime.pos pp) (Nat.ne_of_gt <| Nat.Prime.pos pq)]
    simp only [Finsupp.coe_add, Pi.add_apply]
    have := Function.mt (@Nat.Prime.eq_of_factorization_pos q p pq)
    push_neg at this
    rw [Nat.Prime.factorization_self pp, this <| (ne_of_lt qltp)]
  have cardP := Sylow.card_eq_multiplicity P
  rwa [hdvd,pow_one] at cardP

lemma index_of_P : P.index = q:= by
  have := Subgroup.index_mul_card (P : Subgroup G)
  rw [hG, cardP qltp pp pq P (hG := hG) ,mul_comm] at this
  exact Nat.mul_left_cancel (Nat.Prime.pos pp) this

lemma np_eq_one (hG : Fintype.card G = p * q) (qltp : q < p) : Fintype.card (Sylow p G) = 1 := by
  have := card_sylow_dvd_index P
  rw [index_of_P pp pq hG qltp, Nat.dvd_prime pq] at this
  have h1 := card_sylow_modEq_one p G
  exact Or.elim this (by simp) (fun hx => (by
    rw [hx] at h1
    have := Nat.ModEq.eq_of_lt_of_lt h1 qltp (Nat.Prime.one_lt pp)
    exfalso
    exact ne_of_gt (Nat.Prime.one_lt pq) this
    ))

instance Sylowp.Unique : Unique (Sylow p G) where
  default := P
  uniq := by
    have h1 := np_eq_one pp pq hG qltp (P := P)
    have h2 := Fintype.card_eq_one_iff.1 h1
    rcases h2 with ⟨P',hP⟩
    exact fun a => (Eq.trans (hP a) (eq_comm.1 (hP P) ) )

lemma not_simple : ¬IsSimpleGroup G := by
  apply not_simple_of
  use P
  constructor
  · exact Sylow.normal_of_unique (Sylowp.Unique pp pq hG qltp (P := P))
  · constructor
    · have :=Function.mt (Subgroup.card_eq_iff_eq_top (P : Subgroup G)).2
      rw [←Fintype.card_eq_nat_card, ←Fintype.card_eq_nat_card, cardP qltp pp pq P (hG := hG),hG] at this
      push_neg at this
      have qne1 : q ≠ 1 := Nat.ne_one_iff_exists_prime_dvd.2 ⟨q, ⟨pq, by simp⟩⟩
      have aux : p * q ≠ p := Function.mt (Nat.mul_right_eq_self_iff (Nat.Prime.pos pp)).1 qne1
      exact this (ne_comm.1 aux)
    · exact (Subgroup.one_lt_card_iff_ne_bot (P : Subgroup G)).1 (by
        rw [←Fintype.card_eq_nat_card,cardP qltp pp pq P (hG := hG)]
        exact Nat.Prime.one_lt pp)

end Orderpq
