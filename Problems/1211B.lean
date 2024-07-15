import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic
example {G : Type*} [Group G] (a b c : G) : ∃! x : G, a * x * b = c := by
--First we show the existence of x.
  use a⁻¹ * c * b⁻¹
  group
--Then we show the uniqueness of$x$ by proving if there is another element $y∈G$ meets the condition, then $x=y$.
  constructor
  simp
  intro y hy
--We can do some basic calculating to finish the proof.
  calc
  _=a⁻¹ * (a * y * b) * b⁻¹ :=by group
  _=a⁻¹ * (c) * b⁻¹ :=by rw [hy]
  _=_:= by group
