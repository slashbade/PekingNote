import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

instance (S : Type*) : Mul {f : S → S // f.Bijective} where
  mul := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    use x ∘ y
    exact Function.Bijective.comp hx hy

instance (S : Type*) : One {f : S → S // f.Bijective} where
  one := ⟨id, Function.bijective_id⟩

@[simp]
lemma mul_def {S : Type*} (f g : S → S) (hf : f.Bijective) (hg : g.Bijective) :
  (⟨f, hf⟩ * ⟨g, hg⟩ : {f : S → S // f.Bijective}) = ⟨f ∘ g, Function.Bijective.comp hf hg⟩ := rfl

@[simp]
lemma one_def {S : Type*} : (1 : {f : S → S // f.Bijective}) = ⟨id, Function.bijective_id⟩ := rfl

noncomputable instance (S : Type*) : Group {f : S → S // f.Bijective} where
  mul_assoc := by
    intro ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩
    exact rfl
  one_mul f := rfl
  mul_one f := rfl
  inv := fun ⟨f, hf⟩ => by
    let h_ex := Function.Bijective.existsUnique hf
    constructor; swap;
    . exact fun b => Classical.choose (h_ex b)
    constructor;
    . intro b1 b2; simp; intro hc;
      rw [← (Classical.choose_spec (h_ex b1)).1,
          ← (Classical.choose_spec (h_ex b2)).1];
      congr;
    intro a'; use (f a');
    exact ((Classical.choose_spec (h_ex (f a'))).2 a' (rfl)).symm
  mul_left_inv := fun ⟨f, hf⟩ => by
    let h_ex := Function.Bijective.existsUnique hf
    simp_rw [Subtype.ext_iff, mul_def];
    ext x; simp only [Function.comp_apply];
    exact ((Classical.choose_spec (h_ex (f x))).2 x (rfl)).symm
