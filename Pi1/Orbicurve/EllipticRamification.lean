/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbicurve.Elliptic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.IsGaloisGroup.Basic
public import Mathlib.FieldTheory.Normal.Basic

/-!
# Stabilizers of the punctured hemi-elliptic orbicurve

Let `k` be a field of characteristic zero and `E / k` an elliptic curve in Weierstrass form,
with 2-torsion polynomial `ψ = 4x³ + b₂x² + 2b₄x + b₆ ∈ k[x]`
(`WeierstrassCurve.twoTorsionPolynomial`). The roots of `ψ` are the `x`-coordinates of the
nonzero 2-torsion points (`WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_iff`).

This file proves the statement recorded in the docstring of `Pi1.Orbicurve.Elliptic`: the
stabilizer order of the punctured hemi-elliptic orbicurve `AffOrbicurve.hemi E` at a closed point
`v` of the `x`-line is `2` if `v` divides `ψ` and `1` otherwise
(`AffOrbicurve.hemi_mult_eq`), i.e. the double cover `E ∖ {0} → 𝔸¹` ramifies exactly over the
images of the nonzero 2-torsion points.

## Proof

Put `s = 2y + a₁x + a₃`. In the coordinate ring, `s² = ψ(x)` (`AffOrbicurve.sCoord_sq`).
The extension `k(E) / k(x)` has degree `2` (`AffOrbicurve.finrank_functionField`), hence is
Galois with group `G` of order `2`, and `G` acts on the coordinate ring `B` of `E ∖ {0}`. For a
prime `P` of `B` over `v`, the ramification index is the order of the inertia group of `P`
(`Ideal.card_inertia_eq_ramificationIdxIn`). Since `ψ` has degree `3`, `s ∉ k(x)`
(`AffOrbicurve.sL_ne_algebraMap`), so the nontrivial element of `G` sends `s` to `-s`.

* If `v ∤ ψ` and the nontrivial element were in the inertia group, then `-2s ∈ P`, so `s ∈ P`
  and `ψ = s² ∈ P ∩ k[x] = v`. Hence the inertia group is trivial and the index is `1`.
* If `v ∣ ψ`, write `ψ = u π` with `v = (π)`; `ψ` is squarefree because its discriminant is
  `16 Δ ≠ 0`, so `u ∉ v`. In `B`, `(s)² = (vB)(u)` and `P ∤ (u)`, so the ramification index is
  even (`AffOrbicurve.even_ramificationIdx_of_span_sq`); it is at most `|G| = 2`, hence `2`.
-/

@[expose] public section

universe u

open Polynomial Polynomial.Bivariate

namespace AffOrbicurve

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

attribute [local instance] FractionRing.liftAlgebra

/-- The 2-torsion polynomial `ψ = 4x³ + b₂x² + 2b₄x + b₆ ∈ k[x]`. -/
noncomputable abbrev psi : k[X] := E.twoTorsionPolynomial.toPoly

/-- `s = 2y + a₁x + a₃` in the coordinate ring of `E`. -/
noncomputable def sCoord : E.toAffine.CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine (C 2 * Y + C (C E.a₁ * X + C E.a₃))

omit [CharZero k] [E.IsElliptic] in
/-- `s² = ψ(x)` in the coordinate ring. -/
theorem sCoord_sq : sCoord E ^ 2 = algebraMap k[X] E.toAffine.CoordinateRing (psi E) := by
  have key : (C 2 * Y + C (C E.a₁ * X + C E.a₃) : k[X][Y]) ^ 2 - C (psi E) =
      C (C 4) * E.toAffine.polynomial := by
    simp only [psi, WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly,
      WeierstrassCurve.Affine.polynomial, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [sCoord, ← map_pow, AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.mk_eq_mk.mpr ⟨C (C 4), by rw [key, mul_comm]⟩

omit [CharZero k] [E.IsElliptic] in
/-- `[k(E) : k(x)] = 2`. -/
theorem finrank_functionField :
    Module.finrank (FractionRing k[X]) E.toAffine.FunctionField = 2 := by
  have := isLocalization_algebraMapSubmonoid_of_isAlgebraic k[X] E.toAffine.CoordinateRing
    E.toAffine.FunctionField
  let b := (WeierstrassCurve.Affine.CoordinateRing.basis E.toAffine).localizationLocalization
    (FractionRing k[X]) (nonZeroDivisors k[X]) E.toAffine.FunctionField
  simpa using Module.finrank_eq_card_basis b

/-- The discriminant of `ψ` is `16 Δ ≠ 0`, so `ψ` is separable. -/
theorem psi_separable : (psi E).Separable := by
  set P := E.twoTorsionPolynomial
  let φ := algebraMap k (AlgebraicClosure k)
  have ha : P.a ≠ 0 := by simp [P, WeierstrassCurve.twoTorsionPolynomial]
  have hsplit : (P.toPoly.map φ).Splits := IsAlgClosed.splits _
  have hdisc : P.discr ≠ 0 := by
    rw [WeierstrassCurve.twoTorsionPolynomial_discr]
    exact mul_ne_zero (by norm_num) E.isUnit_Δ.ne_zero
  have hnd := (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mp hdisc
  rw [Cubic.map_roots] at hnd
  have hne : P.toPoly.map φ ≠ 0 :=
    (Polynomial.map_ne_zero_iff φ.injective).mpr (Cubic.ne_zero_of_a_ne_zero ha)
  exact (separable_map φ).mp ((nodup_roots_iff_of_splits hne hsplit).mp hnd)

omit [E.IsElliptic] in
theorem psi_ne_zero : psi E ≠ 0 :=
  Cubic.ne_zero_of_a_ne_zero (by simp [WeierstrassCurve.twoTorsionPolynomial])

/-- `s` in the function field. -/
noncomputable def sL : E.toAffine.FunctionField :=
  algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField (sCoord E)

omit [CharZero k] [E.IsElliptic] in
theorem isIntegral_sL : IsIntegral k[X] (sL E) :=
  (Algebra.IsIntegral.isIntegral (R := k[X]) (sCoord E)).map
    (IsScalarTower.toAlgHom k[X] E.toAffine.CoordinateRing E.toAffine.FunctionField)

/-- `s` in the coordinate ring `B` of `E ∖ {0}` (the integral closure of `k[x]` in `k(E)`). -/
noncomputable def sB : puncturedRing E := ⟨sL E, isIntegral_sL E⟩

omit [CharZero k] [E.IsElliptic] in
theorem sB_sq : sB E ^ 2 = algebraMap k[X] (puncturedRing E) (psi E) := by
  apply Subtype.ext
  change sL E ^ 2 = algebraMap k[X] E.toAffine.FunctionField (psi E)
  rw [sL, ← map_pow, sCoord_sq, ← IsScalarTower.algebraMap_apply]

/-- In a Dedekind domain `S` over `R`, if `(x)² = (v S)(u)` with `u ∉ v`, then every prime `P`
over `v` has even ramification index: `2 ord_P(x) = e(P | v)`. -/
theorem even_ramificationIdx_of_span_sq {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] (v : Ideal R) (P : Ideal S) [P.IsPrime] [hPl : P.LiesOver v]
    (hV0 : v.map (algebraMap R S) ≠ ⊥) {x : S} {u : R} (hu : u ∉ v)
    (hsq : Ideal.span {x} ^ 2 = v.map (algebraMap R S) * Ideal.span {algebraMap R S u}) :
    Even (P.ramificationIdx R) := by
  classical
  have huP : algebraMap R S u ∉ P := by
    intro h; apply hu; rw [hPl.over, Ideal.under, Ideal.mem_comap]; exact h
  have hIu0 : Ideal.span {algebraMap R S u} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h0; exact huP (h0 ▸ P.zero_mem)
  have hcount := congrArg (fun I => (UniqueFactorizationMonoid.normalizedFactors I).count P) hsq
  beta_reduce at hcount
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul,
    UniqueFactorizationMonoid.normalizedFactors_mul hV0 hIu0, Multiset.count_add] at hcount
  have hu_count :
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {algebraMap R S u})).count P
        = 0 := by
    rw [Multiset.count_eq_zero]
    intro hmem
    have hle : Ideal.span {algebraMap R S u} ≤ P :=
      Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem)
    exact huP (hle (Ideal.subset_span rfl))
  rw [hu_count, add_zero,
    ← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count v P hV0] at hcount
  exact ⟨_, by rw [← hcount]; ring⟩

omit [CharZero k] [E.IsElliptic] in
/-- `(s)² = (π)(u)` as ideals of `B` when `ψ = u π`. -/
theorem span_sB_sq {π u : k[X]} (hu : u * π = psi E) :
    Ideal.span {sB E} ^ 2 = Ideal.span {algebraMap k[X] (puncturedRing E) π} *
      Ideal.span {algebraMap k[X] (puncturedRing E) u} := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, sB_sq, ← map_mul,
    mul_comm, hu]

omit [E.IsElliptic] in
theorem natDegree_psi : (psi E).natDegree = 3 :=
  Cubic.natDegree_of_a_ne_zero (by simp [WeierstrassCurve.twoTorsionPolynomial])

omit [E.IsElliptic] in
/-- `s ∉ k(x)`: otherwise `s` would lie in the integrally closed `k[x]`, and `ψ` of degree `3`
would be a square. -/
theorem sL_ne_algebraMap (a : FractionRing k[X]) :
    algebraMap (FractionRing k[X]) E.toAffine.FunctionField a ≠ sL E := by
  intro ha
  have hint : IsIntegral k[X] a := by
    have := isIntegral_sL E
    rw [← ha] at this
    exact (isIntegral_algebraMap_iff
      (algebraMap (FractionRing k[X]) E.toAffine.FunctionField).injective).mp this
  obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have h2 : algebraMap k[X] E.toAffine.FunctionField (r ^ 2) =
      algebraMap k[X] E.toAffine.FunctionField (psi E) := by
    rw [map_pow, IsScalarTower.algebraMap_apply k[X] (FractionRing k[X]), ha, sL, ← map_pow,
      sCoord_sq, ← IsScalarTower.algebraMap_apply]
  have hinj : Function.Injective (algebraMap k[X] E.toAffine.FunctionField) := by
    rw [IsScalarTower.algebraMap_eq k[X] (FractionRing k[X])]
    exact (algebraMap (FractionRing k[X]) E.toAffine.FunctionField).injective.comp
      (IsFractionRing.injective k[X] (FractionRing k[X]))
  have := congrArg natDegree (hinj h2)
  rw [natDegree_pow, natDegree_psi] at this
  omega


open Classical in
/-- **The stabilizers of the punctured hemi-elliptic orbicurve** `(E ∖ {0}) / {±1}`: at a closed
point `v` of the `x`-line the stabilizer order is `2` if `v` divides the 2-torsion polynomial `ψ`
and `1` otherwise. The roots of `ψ` are the `x`-coordinates of the nonzero 2-torsion points
(`WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_iff`), so `E ∖ {0} → 𝔸¹` ramifies
exactly over the images of `E[2] ∖ {0}`. -/
theorem hemi_mult_eq (v : Ideal k[X]) [hv : v.IsMaximal] :
    (hemi E).mult v = if psi E ∈ v then 2 else 1 := by
  classical
  let K := FractionRing k[X]
  let Lf := E.toAffine.FunctionField
  haveI : Algebra.IsQuadraticExtension K Lf := ⟨finrank_functionField E⟩
  haveI : IsGalois K Lf := ⟨⟩
  haveI : IsDedekindDomain (puncturedRing E) := integralClosure.isDedekindDomain k[X] K Lf
  haveI : Module.Finite k[X] (puncturedRing E) :=
    IsIntegralClosure.finite k[X] K Lf (puncturedRing E)
  haveI : IsFractionRing (puncturedRing E) Lf :=
    IsIntegralClosure.isFractionRing_of_finite_extension k[X] K Lf (puncturedRing E)
  haveI := IsGaloisGroup.of_isFractionRing Gal(Lf/K) k[X] (puncturedRing E) K Lf
  have hv0 : v ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hv polynomial_not_isField
  obtain ⟨P, hPmax, hPl⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := puncturedRing E) v
  letI : CharZero v.ResidueField :=
    RingHom.charZero_iff ((algebraMap k[X] v.ResidueField).comp Polynomial.C).injective |>.mp
      inferInstance
  have hcard : Nat.card (P.inertia Gal(Lf/K)) = (hemi E).mult v :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(Lf/K)) v P
  have hG : Nat.card Gal(Lf/K) = 2 := by
    exact (IsGalois.card_aut_eq_finrank K Lf).trans (finrank_functionField E)
  -- the Galois group acts trivially on `k[x]`
  have hψfix : ∀ g : Gal(Lf/K),
      g • algebraMap k[X] (puncturedRing E) (psi E) = algebraMap k[X] (puncturedRing E) (psi E) :=
    fun g => smul_algebraMap g (psi E)
  -- every `g` sends `s` to `± s`
  have hpm : ∀ g : Gal(Lf/K), g • sB E = sB E ∨ g • sB E = -sB E := by
    intro g
    have h1 : (g • sB E) ^ 2 = sB E ^ 2 := by rw [← smul_pow', sB_sq, hψfix]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h1
  -- a nontrivial `g` sends `s` to `-s`
  have hneg : ∀ g : Gal(Lf/K), g ≠ 1 → g • sB E = -sB E := by
    intro g hg
    refine (hpm g).resolve_left fun hfix => ?_
    have hall : ∀ h : Gal(Lf/K), h • sB E = sB E := by
      intro h
      have hmem : ∀ z : Gal(Lf/K), z = 1 ∨ z = g := by
        intro z
        have hc : ({1, g} : Finset Gal(Lf/K)).card = Fintype.card Gal(Lf/K) := by
          rw [Finset.card_pair (Ne.symm hg), ← Nat.card_eq_fintype_card, hG]
        have hz : z ∈ ({1, g} : Finset Gal(Lf/K)) :=
          Finset.eq_univ_of_card _ hc ▸ Finset.mem_univ z
        simpa using hz
      rcases hmem h with rfl | rfl
      · exact one_smul _ _
      · exact hfix
    have hbot : sL E ∈ (⊥ : IntermediateField K Lf) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro h
      exact congrArg Subtype.val (hall h)
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hbot
    exact sL_ne_algebraMap E a ha
  have hvP : ∀ x : k[X], algebraMap k[X] (puncturedRing E) x ∈ P ↔ x ∈ v := by
    intro x
    rw [hPl.over, Ideal.under, Ideal.mem_comap]
  split_ifs with hψ
  · -- `v ∣ ψ`: the ramification index is even and at most `2`
    rw [← hcard]
    have hle : Nat.card (P.inertia Gal(Lf/K)) ≤ 2 := hG ▸ Subgroup.card_le_card_group _
    have hpos : 0 < Nat.card (P.inertia Gal(Lf/K)) := Nat.card_pos
    have he : Nat.card (P.inertia Gal(Lf/K)) = P.ramificationIdx k[X] := by
      rw [hcard]; exact Ideal.ramificationIdxIn_eq_ramificationIdx v P Gal(Lf/K)
    -- `v = (π)`, `ψ = π u` with `u ∉ v`
    obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal v).principal
    rw [Ideal.submodule_span_eq] at hπ
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (hπ ▸ hψ)
    have huv : u ∉ v := by
      intro huv
      rw [hπ, Ideal.mem_span_singleton] at huv
      obtain ⟨w, rfl⟩ := huv
      have hsq : π * π ∣ psi E := ⟨w, by rw [← hu]; ring⟩
      have hunit := (psi_separable E).squarefree π hsq
      exact hv.ne_top (by rw [hπ, Ideal.span_singleton_eq_top]; exact hunit)
    -- ideals of the coordinate ring of `E ∖ {0}`
    have hinj : Function.Injective (algebraMap k[X] (puncturedRing E)) :=
      FaithfulSMul.algebraMap_injective _ _
    have hV : v.map (algebraMap k[X] (puncturedRing E)) =
        Ideal.span {algebraMap k[X] (puncturedRing E) π} := by
      rw [hπ, Ideal.map_span, Set.image_singleton]
    have hV0 : v.map (algebraMap k[X] (puncturedRing E)) ≠ ⊥ := by
      rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    have heven := even_ramificationIdx_of_span_sq v P hV0 (x := sB E) huv
      (by rw [span_sB_sq E hu, hV])
    obtain ⟨m, hm⟩ := heven
    omega
  · -- `v ∤ ψ`: the inertia group is trivial
    rw [← hcard]
    have hbot : P.inertia Gal(Lf/K) = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      by_contra hg1
      have h := hg (sB E)
      rw [hneg g hg1, ← neg_add', ← two_mul, neg_mem_iff] at h
      have hs : sB E ∈ P := by
        rcases hPmax.isPrime.mem_or_mem h with h | h
        · exfalso
          have : algebraMap k[X] (puncturedRing E) 2 ∈ P := by rw [map_ofNat]; exact h
          rw [hvP] at this
          have hu : IsUnit (2 : k[X]) := map_ofNat (Polynomial.C : k →+* k[X]) 2 ▸
            Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : k) ≠ 0))
          exact hv.ne_top (v.eq_top_of_isUnit_mem this hu)
        · exact h
      apply hψ
      rw [← hvP, ← sB_sq E]
      exact P.pow_mem_of_mem hs 2 two_pos
    rw [hbot, Subgroup.card_bot]

end AffOrbicurve
