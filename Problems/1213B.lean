import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
--$\mathrm{Proof.}$
  --We will prove this proposition with induction on $n$.
  induction' n with n ih
  · --1. When $n=0$, the inequality is easy after simple calculation with the definition of factorial.
    rw [fac]
    norm_num
  · --2. When this is true for some $n\in \mathbb{N}$, i.e. we have the ih : $2^{n-1}\leq n!$.
    --Here we devide our goal into two cases according to if $n=0$.
    cases' n with n
    · --(2.1) If $n=0$, we can still figure it with the definition of factorial.
      rw [fac, fac]
      norm_num
    · --(2.2) If $n>0$, we can apply the ih in our new goal : $2^n=2\cdot 2^{n-1}\leq 2 \cdot (n!)\leq (n+1) \cdot (n!)=(n+1)!$ as desire.
      simp only [add_tsub_cancel_right]
      rw [pow_succ, fac, mul_comm]
      apply mul_le_mul
      · exact Nat.le_add_left 2 n
      · exact ih
      · positivity
      · linarith
--Hence, we complete this proof.
--$\square$
