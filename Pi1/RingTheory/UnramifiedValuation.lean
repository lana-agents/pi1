module

public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Unramified algebra maps into valuation rings are determined by their reduction

Let `B` be a formally unramified `R`-algebra of finite type, `K` an `R`-algebra which is a field and
`W ⊆ K` a valuation subring. Two `R`-algebra maps `f g : B → K` with values in `W` which agree
modulo the maximal ideal of `W` are equal (`Algebra.FormallyUnramified.algHom_eq_of_valuation`).

The proof uses the diagonal element `e ∈ B ⊗[R] B`
(`Algebra.FormallyUnramified.elem`): it annihilates all `1 ⊗ b - b ⊗ 1` and maps to `1` under the
multiplication map. Its image under `f ⊗ g` is congruent to `1` modulo the maximal ideal of `W`,
hence nonzero, and it annihilates `g b - f b`.
-/

@[expose] public section

open TensorProduct

namespace Algebra.FormallyUnramified

variable {R B K : Type*} [CommRing R] [CommRing B] [Algebra R B] [Field K] [Algebra R K]

/-- **Unramified maps into a valuation ring are determined modulo its maximal ideal.** -/
theorem algHom_eq_of_valuation [FormallyUnramified R B] [EssFiniteType R B]
    (W : ValuationSubring K) (f g : B →ₐ[R] K) (hf : ∀ b, f b ∈ W) (hg : ∀ b, g b ∈ W)
    (h : ∀ b, W.valuation (f b - g b) < 1) : f = g := by
  let F : B ⊗[R] B →ₐ[R] K := Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _
  have key : ∀ x : B ⊗[R] B, F x ∈ W ∧ W.valuation (F x - f (TensorProduct.lmul' R x)) < 1 := by
    intro x
    induction x with
    | zero => simp
    | tmul a b =>
      refine ⟨?_, ?_⟩
      · simp only [F, Algebra.TensorProduct.lift_tmul]
        exact W.mul_mem _ _ (hf a) (hg b)
      · simp only [F, Algebra.TensorProduct.lift_tmul, TensorProduct.lmul'_apply_tmul, map_mul]
        rw [← mul_sub, map_mul, ← neg_sub, Valuation.map_neg]
        calc W.valuation (f a) * W.valuation (f b - g b) ≤ 1 * W.valuation (f b - g b) :=
              mul_le_mul_left ((W.valuation_le_one_iff _).2 (hf a)) _
          _ < 1 := by rw [one_mul]; exact h b
    | add x y hx hy =>
      refine ⟨by rw [map_add]; exact W.add_mem _ _ hx.1 hy.1, ?_⟩
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx.2 hy.2)
  have hne : F (elem R B) ≠ 0 := by
    intro h0
    have := (key (elem R B)).2
    rw [h0, lmul_elem, map_one, zero_sub, Valuation.map_neg, Valuation.map_one] at this
    exact lt_irrefl _ this
  ext b
  have := congrArg F (one_tmul_sub_tmul_one_mul_elem (R := R) b)
  rw [map_mul, map_sub, map_zero] at this
  simp only [F, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at this
  exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)).symm

end Algebra.FormallyUnramified
