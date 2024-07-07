import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Logic.Equiv.TransferInstance

variable {α :Type} [Fintype α] {a : α}
open Fintype
abbrev Symmgrp (α : Type) := Equiv.Perm α

-- noncomputable def func (f : α ≃ α) (g : α ≃ β) : β ≃ β := Equiv.ofBijective (fun b => g (f (g.symm b)) )
--   ⟨ by dsimp;sorry, sorry⟩
#synth Mul (Symmgrp α)
#check Equiv.Perm.instMul.mul
noncomputable instance Symmgrp_equiv_fin {α : Type} [Fintype α] (h : Fintype.card α = n) :
  Symmgrp α ≃ Symmgrp (Fin n) := by
    dsimp [Symmgrp,Equiv.Perm]
    have := Fintype.equivFinOfCardEq h
    exact Equiv.equivCongr this this

noncomputable instance  {α : Type} [Fintype α] (h : Fintype.card α = n) :
  Symmgrp α ≃* Symmgrp (Fin n) := {
    Symmgrp_equiv_fin h with
    map_mul' := by
      intro x y;
      simp only [Equiv.toFun_as_coe];
      ext fn
      simp only [Equiv.Perm.coe_mul,Function.comp_apply]
      rw [Equiv.Perm.mul_def]
      sorry
  }

-- theorem Symmgrp_equiv_iff {α β : Type} [Fintype α] [Fintype β] :
--   (Symmgrp α ) ≃ (Symmgrp β) → Fintype.card α = Fintype.card β := sorry

noncomputable instance Symmgrp_equiv_of_card_eq {α β : Type} [Fintype α] [Fintype β] (h : Fintype.card α = Fintype.card β):
   (Symmgrp α ) ≃ (Symmgrp β) := sorry


instance stabilizer_eq : MulAction.stabilizer (Symmgrp α) a ≃ Symmgrp (Fin (card α - 1)) := sorry

#check alternatingGroup
#check Fintype.card_perm
#check alternatingGroup.normal
