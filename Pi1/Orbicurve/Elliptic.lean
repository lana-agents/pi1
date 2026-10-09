/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbicurve.IntegralClosure
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Once-punctured elliptic curves, their `±1`-quotients, and [CanLift], Proposition 2.7

Let `k` be a field of characteristic zero and `E / k` an elliptic curve with Weierstrass
function field `k(E) = k(x, y)`.

* `AffOrbicurve.punctured E`: the once-punctured elliptic curve `X = E ∖ {0}`. Its coarse
  space is `X` itself, the normalization of the `x`-line `A¹ = Spec k[x]` in `k(E)` (the
  point `0 = ∞` is the unique point of `E` over `x = ∞`), with trivial stabilizers.
* `AffOrbicurve.hemi E`: the *punctured hemi-elliptic orbicurve* `X / {±1}` ([CanLift],
  Definition 2.6(ii)), the quotient stack of `X` by `[-1] : (x, y) ↦ (x, -y - a₁x - a₃)`.
  Its coarse space is `X / {±1} = Spec k[x] = A¹` (the `x`-line), and the stabilizer order at
  a closed point `v` of `A¹` is the order of the stabilizer of a point of `X` over `v`, i.e.
  the ramification index `e(w | v)` of the double cover `X → A¹` at any `w | v`
  (`Ideal.ramificationIdxIn`); it is `2` at the three points `x(P)`, `P ∈ E[2] ∖ {0}`, and `1`
  elsewhere.
* `AffOrbicurve.excJ`: the four exceptional `j`-invariants
  `0, 1728, 2¹⁴·31³/5³, 2²·73³/3⁴`. By [CanLift], Proposition 2.7 there are exactly four
  isomorphism classes of arithmetic punctured hemi-elliptic orbicurves over an algebraically
  closed field of characteristic `0`; they correspond to Takeuchi's four arithmetic Fuchsian
  groups of signature `(1; ∞)` (K. Takeuchi, *Arithmetic Fuchsian groups with signature
  (1; e)*, J. Math. Soc. Japan 35 (1983)), whose quotient curves have the canonical models
  over `ℚ` of J. Sijsling, *Canonical models of arithmetic (1; ∞)-curves*
  (arXiv:1707.01158), Table 4: `y² = x³ − 44x² − 16x` (LMFDB 20.a1, `j = 2¹⁴·31³/5³`),
  `y² = x³ − 4x² − 384x − 2304` (24.a3, `j = 2²·73³/3⁴`), `y² = x(x² − 256)` (32.a4,
  `j = 1728`) and `y² = x³ − 1728` (36.a3, `j = 0`).
* `AffOrbicurve.CanLift27`: **[CanLift], Proposition 2.7** (with Proposition 2.3(i) to pass
  from `k̄` to `k`): if `j(E)` is not exceptional, then the `k`-core of `E ∖ {0}` is the
  punctured hemi-elliptic orbicurve `(E ∖ {0}) / {±1}`.
* `AffOrbicurve.CanLift27Arith`: the converse part of [CanLift], Proposition 2.7: if `j(E)`
  is exceptional, then `E ∖ {0}` is `k`-arithmetic (has no `k`-core).

These two statements are not proved here.
-/

@[expose] public section

universe u

open Polynomial

namespace AffOrbicurve

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

attribute [local instance] FractionRing.liftAlgebra

instance : Module.Finite k[X] E.toAffine.CoordinateRing :=
  Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis E.toAffine)


instance : FaithfulSMul k[X] E.toAffine.CoordinateRing := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro p q h
  have h' : (p - q) • (1 : E.toAffine.CoordinateRing) + (0 : k[X]) •
      WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine Polynomial.X = 0 := by
    rw [zero_smul, add_zero, sub_smul, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one]
    exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp (WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero h').1

instance : FaithfulSMul k[X] E.toAffine.FunctionField := by
  rw [faithfulSMul_iff_algebraMap_injective,
    IsScalarTower.algebraMap_eq k[X] E.toAffine.CoordinateRing E.toAffine.FunctionField]
  exact (IsFractionRing.injective E.toAffine.CoordinateRing E.toAffine.FunctionField).comp
    (FaithfulSMul.algebraMap_injective _ _)

instance : FiniteDimensional (FractionRing k[X]) E.toAffine.FunctionField :=
  have := isLocalization_algebraMapSubmonoid_of_isAlgebraic k[X] E.toAffine.CoordinateRing
    E.toAffine.FunctionField
  Module.Finite.of_isLocalization k[X] E.toAffine.CoordinateRing (nonZeroDivisors k[X])

omit [CharZero k] [E.IsElliptic] in
/-- The `x`-line `A¹ = Spec k[x]` is a curve. -/
lemma polynomial_not_isField : ¬ IsField k[X] := Polynomial.not_isField k

/-- **The once-punctured elliptic curve** `E ∖ {0}`: the normalization of the `x`-line in the
function field `k(E)` (a scheme: all stabilizers are trivial). -/
noncomputable def punctured : AffOrbicurve k :=
  ofIntegralClosureScheme k[X] (FractionRing k[X]) E.toAffine.FunctionField
    polynomial_not_isField

/-- The coordinate ring of `E ∖ {0}` as a `k[x]`-algebra (the double cover `E ∖ {0} → A¹`). -/
abbrev puncturedRing : Type u := integralClosure k[X] E.toAffine.FunctionField

/-- **The punctured hemi-elliptic orbicurve** `(E ∖ {0}) / {±1}` ([CanLift], Definition
2.6(ii)): coarse space the `x`-line `Spec k[x]`, with stabilizer order at `v` the
ramification index of `E ∖ {0} → A¹` over `v`. -/
noncomputable def hemi : AffOrbicurve k where
  A := k[X]
  not_isField := polynomial_not_isField
  mult v := v.ramificationIdxIn (puncturedRing E)
  mult_pos v hv := by
    have := integralClosure_finite k[X] (FractionRing k[X]) E.toAffine.FunctionField
    obtain ⟨P, hP, hPl⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := puncturedRing E) v
    have hex : ∃ P : Ideal (puncturedRing E), P.IsPrime ∧ P.LiesOver v := ⟨P, hP.isPrime, hPl⟩
    rw [Ideal.ramificationIdxIn, dif_pos hex]
    have := hex.choose_spec.1
    exact Ideal.ramificationIdx_pos _ _
  finite_mult := by
    have := integralClosure_finite k[X] (FractionRing k[X]) E.toAffine.FunctionField
    have := integralClosure_isDedekindDomain k[X] (FractionRing k[X]) E.toAffine.FunctionField
    exact finite_setOf_ramificationIdxIn_ne_one

/-- **The exceptional `j`-invariants** of [CanLift], Proposition 2.7: the `j`-invariants of
the four arithmetic once-punctured elliptic curves (Takeuchi; Sijsling, Table 4):
`0, 1728 = 2⁶·3³, 488095744/125 = 2¹⁴·31³/5³, 1556068/81 = 2²·73³/3⁴`. -/
def excJ : Finset ℚ := {0, 1728, 488095744 / 125, 1556068 / 81}

/-- **[CanLift], Proposition 2.7** (the non-arithmetic case, over any field of characteristic
zero via [CanLift], Proposition 2.3(i)): if `j(E)` is not one of the four exceptional values,
the punctured hemi-elliptic orbicurve `(E ∖ {0}) / {±1}` is the `k`-core of `E ∖ {0}`. -/
def CanLift27 : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic],
    (∀ c ∈ excJ, E.j ≠ (c : k)) → IsCoreOf (punctured E) (hemi E)

/-- **[CanLift], Proposition 2.7** (the arithmetic case, over any field of characteristic zero
via [CanLift], Proposition 2.3(i)): if `j(E)` is one of the four exceptional values, then
`E ∖ {0}` is `k`-arithmetic: it has no `k`-core. -/
def CanLift27Arith : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic],
    (∃ c ∈ excJ, E.j = (c : k)) → IsArithmetic (punctured E)

end AffOrbicurve
