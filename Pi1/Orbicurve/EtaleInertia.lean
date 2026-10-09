/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbicurve.ValuationInertia
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# Étaleness of maps of coordinate rings via inertia groups

Let `k` be a field of characteristic `0`, `t ∈ Ω` transcendental over `k` and `Ω / K₀`
(`K₀ = k(t)`) Galois. For intermediate fields `L ⊆ N` of `Ω / K₀`, finite over `K₀`, the
inclusion `coordRing k t L → coordRing k t N` of the coordinate rings of the normalizations of
the `t`-line is finite (`AffOrbicurve.module_finite_of_charZero`), and it is étale if and only
if, for every valuation subring `W` of `Ω` centered on the `t`-line, every element of the
inertia group of `W` fixing `L` fixes `N` (`AffOrbicurve.etale_iff_inertia`):

  `Etale(coordRing k t L → coordRing k t N) ↔ ∀ W, I_W ∩ Aut(Ω / L) ⊆ Aut(Ω / N)`.

Every maximal ideal of a coordinate ring is the center of a valuation subring of `Ω` centered on
the `t`-line (`AffOrbicurve.exists_isCentered_centerIdeal_eq`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

section Centers

/-- **Every maximal ideal of a coordinate ring is a center**: for a maximal ideal `Q` of
`coordRing k t M` there is a valuation subring `W` of `Ω` centered on the `t`-line with
`u_W(M) = Q` (extend the local ring at `Q` to a valuation subring of `Ω`). -/
theorem exists_isCentered_centerIdeal_eq (M : IntermediateField (K₀ k t) Ω)
    (Q : Ideal (coordRing k t M)) [hQ : Q.IsMaximal] :
    ∃ (W : ValuationSubring Ω) (hW : IsCentered k t W), centerIdeal hW M = Q := by
  let R := Localization.AtPrime Q
  letI : Algebra (coordRing k t M) R := OreLocalization.instAlgebra
  haveI : IsLocalization.AtPrime R Q := Localization.isLocalization
  have hunit : ∀ s : Q.primeCompl, IsUnit (toΩ t M s) := by
    intro s
    refine IsUnit.mk0 _ fun h0 => s.2 ?_
    rw [← map_zero (toΩ t M)] at h0
    rw [toΩ_injective M h0]
    exact Q.zero_mem
  let f : R →+* Ω := IsLocalization.lift (M := Q.primeCompl) (S := R) hunit
  have hf : ∀ a, f (algebraMap _ R a) = toΩ t M a := IsLocalization.lift_eq hunit
  obtain ⟨W, hmem, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hA : ∀ a : coordRing k t M, toΩ t M a ∈ W := fun a => by
    rw [← hf]; exact hmem _
  have hW : IsCentered k t W := by
    refine ⟨fun c => ?_, ?_⟩
    · exact hA (algebraMap k (coordRing k t M) c)
    · exact hA (algebraMap (A₀ k t) (coordRing k t M) ⟨t, Algebra.subset_adjoin rfl⟩)
  refine ⟨W, hW, (hQ.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun b hb => ?_).symm⟩
  rw [mem_centerIdeal_iff_mem_nonunits]
  intro hu
  have hb' : algebraMap _ R b ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff R Q]
    exact hb
  apply hb'
  apply hloc.map_nonunit
  have he : (f.codRestrict W.toSubring hmem) (algebraMap _ R b) =
      (⟨toΩ t M b, toΩ_mem hW M b⟩ : W) := Subtype.ext (hf b)
  rw [he]
  exact hu

end Centers

section Fix

lemma eq_one_of_forall_coordRing (M : IntermediateField (K₀ k t) Ω)
    [FiniteDimensional (K₀ k t) M] (ρ : M ≃ₐ[K₀ k t] M)
    (h : ∀ b : coordRing k t M, ρ (b : M) = b) : ρ = 1 := by
  haveI := isFractionRing_coordRing t M
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (coordRing k t M) x
  rw [map_div₀]
  exact congrArg₂ (fun y z : M => ((y / z : M) : Ω)) (h a) (h b)

/-- If the center of `W` on `M` is zero (`W` is trivial on `k(t)`), the inertia group of `W`
fixes `M`. -/
lemma fixes_of_centerIdeal_eq_bot {W : ValuationSubring Ω} (hW : IsCentered k t W)
    (M : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) M] [Normal (K₀ k t) M]
    (hne : centerIdeal hW M = ⊥) {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) :
    ∀ x ∈ M, σ x = x := by
  have hρ := restrictNormal_mem_inertia hW M hσ
  rw [hne] at hρ
  have h1 : σ.restrictNormal M = 1 := eq_one_of_forall_coordRing M _ fun b => by
    have h2 := AddSubgroup.mem_inertia.mp hρ b
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_bot, sub_eq_zero] at h2
    exact congrArg Subtype.val h2
  intro x hx
  have h2 := congrArg (fun ρ : M ≃ₐ[K₀ k t] M => ((ρ ⟨x, hx⟩ : M) : Ω)) h1
  simpa using h2

end Fix

variable [CharZero k]

section Finite

instance charZero_K₀ : CharZero (K₀ k t) :=
  charZero_of_injective_algebraMap (algebraMap k (K₀ k t)).injective

lemma isSeparable_of_charZero (N : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) N] :
    Algebra.IsSeparable (K₀ k t) N :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- The coordinate ring of `N` is finite over the coordinate ring of `L ⊆ N`. -/
theorem module_finite_of_charZero (ht : Transcendental k t) {L N : IntermediateField (K₀ k t) Ω}
    (hLN : L ≤ N) [FiniteDimensional (K₀ k t) N] :
    @Module.Finite (coordRing k t L) (coordRing k t N) _ _ (algRing t hLN).toModule :=
  haveI := isSeparable_of_charZero N
  module_finite_ringMap t ht hLN

end Finite

section Etale

set_option maxHeartbeats 1000000 in
/-- The étale criterion, given a finite Galois extension `M ⊇ N` of `k(t)`. -/
theorem etale_iff_inertia_of_le [IsGalois (K₀ k t) Ω] (ht : Transcendental k t)
    {L N M : IntermediateField (K₀ k t) Ω} (hLN : L ≤ N) (hNM : N ≤ M)
    [FiniteDimensional (K₀ k t) N] [FiniteDimensional (K₀ k t) M] [IsGalois (K₀ k t) M] :
    (letI := algRing t hLN; Algebra.Etale (coordRing k t L) (coordRing k t N)) ↔
      ∀ W : ValuationSubring Ω, IsCentered k t W →
        GaloisPi1.inertia (P := K₀ k t) W ∩ (L.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)) ⊆
          N.fixingSubgroup := by
  haveI := isSeparable_of_charZero N
  haveI : FiniteDimensional (K₀ k t) L :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hLN).toLinearMap
      (IntermediateField.inclusion hLN).injective
  haveI := isSeparable_of_charZero L
  haveI := isDedekindDomain_ring t ht L
  haveI := isDedekindDomain_ring t ht N
  have key : ∀ (W : ValuationSubring Ω) (hW : IsCentered k t W), centerIdeal hW M ≠ ⊥ →
      ((letI := algRing t hLN; ((centerIdeal hW M).comap (ringMap t hNM)).ramificationIdx
        (coordRing k t L)) = 1 ↔
        GaloisPi1.inertia (P := K₀ k t) W ∩ (L.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)) ⊆
          N.fixingSubgroup) := by
    intro W hW hne
    haveI := isMaximal_centerIdeal ht hW M hne
    rw [ramificationIdx_eq_one_iff t ht hLN hNM]
    constructor
    · rintro h σ ⟨hσ, hσL⟩
      have h1 := h (restrictNormal_mem_inertia_inf_fixSub hW M hσ hσL)
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_
      have h2 := congrArg (fun y : M => (y : Ω)) (h1 ⟨x, hNM hx⟩ hx)
      simpa using h2
    · intro h τ hτ
      obtain ⟨σ, hσ, hσL, rfl⟩ :=
        exists_mem_inertia_fixingSubgroup_restrictNormal_eq ht hW (hLN.trans hNM) hne τ hτ
      exact restrictNormal_mem_fixSub M (h ⟨hσ, hσL⟩)
  letI iR := algRing t hLN
  letI : SMul (coordRing k t L) (coordRing k t N) := iR.toSMul
  letI : Module (coordRing k t L) (coordRing k t N) := iR.toModule
  haveI := module_finite_of_charZero ht hLN
  haveI : Algebra.IsIntegral (coordRing k t L) (coordRing k t N) := ⟨ringMap_isIntegral t hLN⟩
  haveI : Module.IsTorsionFree (coordRing k t L) (coordRing k t N) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact ringMap_injective t hLN
  constructor
  · intro hét W hW σ ⟨hσ, hσL⟩
    by_cases hne : centerIdeal hW M = ⊥
    · exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx =>
        fixes_of_centerIdeal_eq_bot hW M hne hσ x (hNM hx)
    · refine (key W hW hne).mp ?_ ⟨hσ, hσL⟩
      let P := (centerIdeal hW M).comap (ringMap t hNM)
      haveI : P.IsPrime := Ideal.comap_isPrime _ _
      haveI : Algebra.IsUnramifiedAt (coordRing k t L) P :=
        (Algebra.formallyUnramified_iff_forall.mp inferInstance) ⟨P, inferInstance⟩
      exact Ideal.ramificationIdx_eq_one P (coordRing k t L)
  · intro h
    haveI : Algebra.FinitePresentation (coordRing k t L) (coordRing k t N) :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    haveI : CharZero (coordRing k t L) :=
      charZero_of_injective_algebraMap (algebraMap k (coordRing k t L)).injective
    haveI : Algebra.FormallyUnramified (coordRing k t L) (coordRing k t N) := by
      rw [Algebra.formallyUnramified_iff_forall]
      rintro ⟨q, hq⟩
      by_cases hq0 : q = ⊥
      · subst hq0
        exact Algebra.isUnramifiedAt_bot
      haveI hqmax : q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hq0 hq
      obtain ⟨Q, hQ, hQq⟩ := letI := algRing t hNM
        haveI : Algebra.IsIntegral (coordRing k t N) (coordRing k t M) :=
          ⟨ringMap_isIntegral t hNM⟩
        Ideal.exists_ideal_over_maximal_of_isIntegral (S := coordRing k t M) q (by
          intro x hx
          rw [RingHom.mem_ker] at hx
          rw [ringMap_injective t hNM (hx.trans (map_zero _).symm)]
          exact q.zero_mem)
      change Q.comap (ringMap t hNM) = q at hQq
      obtain ⟨W, hW, hWQ⟩ := exists_isCentered_centerIdeal_eq M Q
      have hne : centerIdeal hW M ≠ ⊥ := by
        rw [hWQ]
        rintro rfl
        apply hq0
        rw [← hQq, ← RingHom.ker_eq_comap_bot]
        exact (RingHom.injective_iff_ker_eq_bot _).mp (ringMap_injective t hNM)
      have he := (key W hW hne).mpr (h W hW)
      rw [hWQ, hQq] at he
      haveI : CharZero (q.under (coordRing k t L)).ResidueField :=
        charZero_of_injective_algebraMap
          (algebraMap k (q.under (coordRing k t L)).ResidueField).injective
      exact Ideal.ramificationIdx_eq_one_iff.mp he
    exact Algebra.Etale.of_formallyUnramified_of_flat

/-- **The étale criterion**: for intermediate fields `L ⊆ N` of `Ω / k(t)`, finite over `k(t)`
(characteristic `0`, `Ω / k(t)` Galois), the inclusion of coordinate rings
`coordRing k t L → coordRing k t N` is étale if and only if for every valuation subring `W` of
`Ω` centered on the `t`-line, every element of the inertia group `I_W` fixing `L` fixes `N`. -/
theorem etale_iff_inertia [IsGalois (K₀ k t) Ω] (ht : Transcendental k t)
    {L N : IntermediateField (K₀ k t) Ω} (hLN : L ≤ N) [FiniteDimensional (K₀ k t) N] :
    (letI := algRing t hLN; Algebra.Etale (coordRing k t L) (coordRing k t N)) ↔
      ∀ W : ValuationSubring Ω, IsCentered k t W →
        GaloisPi1.inertia (P := K₀ k t) W ∩ (L.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)) ⊆
          N.fixingSubgroup :=
  haveI : FiniteDimensional (K₀ k t) (normalClosure (K₀ k t) N Ω) :=
    normalClosure.is_finiteDimensional _ _ _
  haveI : IsGalois (K₀ k t) (normalClosure (K₀ k t) N Ω) := IsGalois.normalClosure _ _ _
  etale_iff_inertia_of_le ht hLN (IntermediateField.le_normalClosure N)

end Etale

end AffOrbicurve
