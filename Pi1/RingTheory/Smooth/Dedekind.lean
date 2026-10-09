/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Etale.Field

/-!
# Dedekind domains of finite type over a perfect field are smooth

Let `k` be a perfect field and `R` a Dedekind domain of finite type over `k` (an affine regular
curve, or a finite separable field extension of `k`). Then `R` is smooth over `k`
(`Algebra.smooth_of_isDedekindDomain`).

Proof (étale-local): the smooth locus is open (`Algebra.isOpen_smoothLocus`), so it suffices to
check smoothness at the maximal ideals (`Algebra.formallySmooth_of_forall_isSmoothAt_isMaximal`).
At a maximal ideal `m` with `m Rₘ = (π)` and `π ≠ 0`, view `R` as a `k[T]`-algebra via `T ↦ π`.
Then `π` is transcendental over `k`, so `R` is flat over the PID `k[T]`, and `R` is unramified
at `m` over `k[T]` (`(T) Rₘ = m Rₘ`, and `κ(m)` is finite, hence separable, over `k`).
So `Rₘ` is formally étale over `k[T]`, hence formally smooth over `k`
(`Algebra.isSmoothAt_of_maximalIdeal_eq_span`).

We also record `IsDedekindDomain.ringKrullDim_eq_one`: a Dedekind domain which is not a field has
Krull dimension `1`.
-/

@[expose] public section

open IsLocalRing Polynomial

namespace Algebra

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- For a finitely presented algebra, smoothness at all maximal ideals implies formal smoothness:
the smooth locus is open, hence stable under generization. -/
theorem formallySmooth_of_forall_isSmoothAt_isMaximal {A : Type*} [CommRing A] [Algebra R A]
    [FinitePresentation R A] (h : ∀ (m : Ideal A) [m.IsMaximal], IsSmoothAt R m) :
    FormallySmooth R A := by
  rw [← smoothLocus_eq_univ_iff]
  refine Set.eq_univ_iff_forall.2 fun p ↦ ?_
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  have hm' : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈ smoothLocus R A := h m
  exact isOpen_smoothLocus.stableUnderGeneralization
    ((PrimeSpectrum.le_iff_specializes p ⟨m, hm.isPrime⟩).1 hpm) hm'

/-- A nonzero element of a maximal ideal of a domain over a field is transcendental. -/
theorem transcendental_of_mem_isMaximal [IsDomain R] {m : Ideal R} [m.IsMaximal] {π : R}
    (hπ : π ∈ m) (hπ0 : π ≠ 0) : Transcendental k π := by
  intro halg
  have hu : IsUnit π := (halg.isIntegral).isUnit hπ0
  exact (Ideal.IsMaximal.ne_top ‹_›) (Ideal.eq_top_of_isUnit_mem _ hπ hu)

/-- The residue field at a maximal ideal of an algebra of finite type over a field is algebraic. -/
theorem isAlgebraic_residueField [FiniteType k R] (m : Ideal R) [m.IsMaximal] :
    Algebra.IsAlgebraic k m.ResidueField := by
  letI := Ideal.Quotient.field m
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  have e : (R ⧸ m) ≃ₐ[k] m.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom k (R ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  exact e.isAlgebraic

/-- **Smoothness at a maximal ideal with principal maximal ideal.** Let `R` be a domain of finite
type over a perfect field `k` and `m` a maximal ideal with `m Rₘ = (π)` for some `0 ≠ π ∈ R`.
Then `R` is smooth over `k` at `m`. -/
theorem isSmoothAt_of_maximalIdeal_eq_span [PerfectField k] [FiniteType k R] [IsDomain R]
    (m : Ideal R) [m.IsMaximal] {π : R} (hπ0 : π ≠ 0) (hπm : π ∈ m)
    (hπ : maximalIdeal (Localization.AtPrime m) =
      Ideal.span {algebraMap R (Localization.AtPrime m) π}) :
    IsSmoothAt k m := by
  letI : Algebra k[X] R := (aeval π).toRingHom.toAlgebra
  haveI : IsScalarTower k k[X] R := IsScalarTower.of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  haveI : FiniteType k[X] R := .of_restrictScalars_finiteType k k[X] R
  haveI : FinitePresentation k[X] R := FinitePresentation.of_finiteType.1 inferInstance
  have hinj : Function.Injective (algebraMap k[X] R) :=
    transcendental_iff_injective.1 (transcendental_of_mem_isMaximal (k := k) hπm hπ0)
  haveI : FaithfulSMul k[X] R := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Module.Flat k[X] R := inferInstance
  let p := m.under k[X]
  letI := Localization.AtPrime.algebraOfLiesOver p m
  haveI : IsUnramifiedAt k[X] m := by
    rw [isUnramifiedAt_iff_map_eq k[X] p m]
    refine ⟨?_, ?_⟩
    · haveI := isAlgebraic_residueField (k := k) m
      haveI : Algebra.IsSeparable k m.ResidueField :=
        Algebra.IsAlgebraic.isSeparable_of_perfectField
      exact Algebra.isSeparable_tower_top_of_isSeparable k p.ResidueField m.ResidueField
    · refine le_antisymm ?_ ?_
      · rw [IsScalarTower.algebraMap_eq k[X] R, ← Ideal.map_map,
          ← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.map_mono Ideal.map_comap_le
      · rw [hπ, Ideal.span_le, Set.singleton_subset_iff]
        have hX : (X : k[X]) ∈ p := by
          change algebraMap k[X] R X ∈ m
          simpa [RingHom.algebraMap_toAlgebra] using hπm
        have := Ideal.mem_map_of_mem (algebraMap k[X] (Localization.AtPrime m)) hX
        rwa [IsScalarTower.algebraMap_apply k[X] R (Localization.AtPrime m),
          show algebraMap k[X] R X = π by simp [RingHom.algebraMap_toAlgebra]] at this
  haveI : IsEtaleAt k[X] m := IsEtaleAt.of_isUnramifiedAt_of_flat m
  exact FormallySmooth.comp k k[X] (Localization.AtPrime m)

/-- **A Dedekind domain of finite type over a perfect field is smooth.** -/
theorem smooth_of_isDedekindDomain [PerfectField k] [IsDedekindDomain R] [FiniteType k R] :
    Smooth k R := by
  haveI : FinitePresentation k R := FinitePresentation.of_finiteType.1 inferInstance
  refine ⟨?_, inferInstance⟩
  by_cases hF : IsField R
  · letI := hF.toField
    haveI : Module.Finite k R := finite_of_finite_type_of_isJacobsonRing k R
    exact inferInstance
  refine formallySmooth_of_forall_isSmoothAt_isMaximal fun m hm ↦ ?_
  have hm0 : m ≠ ⊥ := fun h ↦ hF (Ring.isField_iff_maximal_bot.mpr (h ▸ hm))
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hm0
    (Localization.AtPrime m)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime m)
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl ϖ
  have hspan : maximalIdeal (Localization.AtPrime m) =
      Ideal.span {algebraMap R (Localization.AtPrime m) a} := by
    rw [hϖ.maximalIdeal_eq, IsLocalization.mk'_eq_mul_mk'_one,
      Ideal.span_singleton_mul_right_unit]
    exact IsUnit.of_mul_eq_one (algebraMap R _ s) (by rw [IsLocalization.mk'_spec, map_one])
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hϖ.ne_zero (by simp)
  have ham : a ∈ m := by
    have : algebraMap R (Localization.AtPrime m) a ∈ maximalIdeal _ :=
      hspan ▸ Ideal.subset_span rfl
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m a).1 this
  exact isSmoothAt_of_maximalIdeal_eq_span m ha0 ham hspan

end Algebra

/-- A Dedekind domain which is not a field has Krull dimension `1`. -/
theorem IsDedekindDomain.ringKrullDim_eq_one {R : Type*} [CommRing R] [IsDedekindDomain R]
    (h : ¬ IsField R) : ringKrullDim R = 1 := by
  apply eq_of_le_of_not_lt ?_ fun h' ↦ h ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    exact .mk₁' fun _ hI hI' ↦ hI'.isMaximal hI
  · have h'' : ringKrullDim R ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain
