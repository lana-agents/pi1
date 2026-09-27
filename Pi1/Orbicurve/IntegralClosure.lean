module

public import Pi1.Orbicurve.Core
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Affine orbicurves from integral closures

The coarse spaces of the orbicurves we construct are normalizations: the integral closure `C`
of a Dedekind domain `A₀` of finite type over `k` (not a field) in a finite separable extension
`L` of its fraction field. This file records that such a `C` is again a Dedekind domain of
finite type over `k` which is not a field (`AffOrbicurve.ofIntegralClosure`), and that only
finitely many maximal ideals of `A₀` ramify in `C` (`finite_setOf_ramificationIdxIn_ne_one`,
from the different ideal).
-/

@[expose] public section

universe u

open Ideal

namespace AffOrbicurve

variable {k : Type u} [Field k]

section IntegralClosure

variable (A₀ : Type u) [CommRing A₀] [IsDedekindDomain A₀] [Algebra k A₀]
  [Algebra.FiniteType k A₀]
  (K L : Type u) [Field K] [Field L] [Algebra A₀ K] [IsFractionRing A₀ K] [Algebra K L]
  [Algebra A₀ L] [IsScalarTower A₀ K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Algebra k L] [IsScalarTower k A₀ L]

include K

lemma integralClosure_isDedekindDomain : IsDedekindDomain (integralClosure A₀ L) :=
  integralClosure.isDedekindDomain A₀ K L

lemma integralClosure_finite : Module.Finite A₀ (integralClosure A₀ L) :=
  IsIntegralClosure.finite A₀ K L (integralClosure A₀ L)

lemma integralClosure_finiteType : Algebra.FiniteType k (integralClosure A₀ L) := by
  have := integralClosure_finite A₀ K L
  exact Algebra.FiniteType.trans (S := A₀) inferInstance inferInstance

omit [IsDedekindDomain A₀] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
lemma integralClosure_not_isField (h : ¬ IsField A₀) : ¬ IsField (integralClosure A₀ L) := by
  intro hC
  refine h (isField_of_isIntegral_of_isField ?_ hC)
  intro a b hab
  have hinj : Function.Injective (algebraMap A₀ L) := by
    rw [IsScalarTower.algebraMap_eq A₀ K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A₀ K)
  apply hinj
  have := congrArg (fun c : integralClosure A₀ L => (c : L)) hab
  simpa using this

/-- **The affine orbicurve with coarse space the normalization** of `Spec A₀` in `L` and
stabilizer orders `mult`. -/
noncomputable def ofIntegralClosure (h : ¬ IsField A₀) (mult : Ideal (integralClosure A₀ L) → ℕ)
    (mult_pos : ∀ v, v.IsMaximal → 0 < mult v)
    (finite_mult : {v : Ideal (integralClosure A₀ L) | v.IsMaximal ∧ mult v ≠ 1}.Finite) :
    AffOrbicurve k :=
  letI := integralClosure_isDedekindDomain A₀ K L
  letI := integralClosure_finiteType A₀ K L (k := k)
  { A := integralClosure A₀ L
    not_isField := integralClosure_not_isField A₀ K L h
    mult := mult
    mult_pos := mult_pos
    finite_mult := finite_mult }

/-- **The normalization of `Spec A₀` in `L`, as a scheme** (all stabilizers trivial). -/
noncomputable def ofIntegralClosureScheme (h : ¬ IsField A₀) : AffOrbicurve k :=
  ofIntegralClosure A₀ K L h (fun _ => 1) (fun _ _ => Nat.one_pos) (by simp)

end IntegralClosure


section Localization

/-- The fraction field of a domain `S` algebraic over a domain `R` is its localization at the
nonzero elements of `R`. -/
theorem isLocalization_algebraMapSubmonoid_of_isAlgebraic (R S L : Type*) [CommRing R]
    [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsAlgebraic R S]
    [FaithfulSMul R S] [Field L] [Algebra S L] [IsFractionRing S L] :
    IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) L where
  map_units := by
    rintro ⟨_, r, hr, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    rw [Ne, IsFractionRing.to_map_eq_zero_iff (R := S)]
    rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R S)]
    exact nonZeroDivisors.ne_zero hr
  surj z := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) z
    obtain ⟨c, d, hd, h⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul R a (nonZeroDivisors.ne_zero hb)
    refine ⟨⟨c, ⟨algebraMap R S d, d, mem_nonZeroDivisors_of_ne_zero hd, rfl⟩⟩, ?_⟩
    have hb' : algebraMap S L b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr (nonZeroDivisors.ne_zero hb)
    simp only
    rw [Algebra.smul_def] at h
    field_simp
    rw [← map_mul, ← map_mul, mul_comm a, h]
  exists_of_eq {x y} h := ⟨1, by simpa using IsFractionRing.injective S L h⟩

end Localization

section Ramified

attribute [local instance] FractionRing.liftAlgebra

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
  [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S] [FaithfulSMul R S]
  [Module.Finite R S]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

/-- Only finitely many maximal ideals of a Dedekind domain `A` ramify in a finite separable
extension `B`: a prime `P` of `B` with `e(P) ≥ 2` divides the different ideal, which is
nonzero. -/
lemma finite_setOf_ramificationIdxIn_ne_one :
    {v : Ideal R | v.IsMaximal ∧ v.ramificationIdxIn S ≠ 1}.Finite := by
  classical
  have hD : differentIdeal R S ≠ ⊥ := differentIdeal_ne_bot
  let T : Finset (Ideal S) :=
    (UniqueFactorizationMonoid.normalizedFactors (differentIdeal R S)).toFinset
  refine ((T.finite_toSet.image (fun P => P.comap (algebraMap R S))).union
    (Set.finite_singleton (⊥ : Ideal R))).subset ?_
  rintro v ⟨hv, hne⟩
  by_cases hvb : v = ⊥
  · exact Or.inr hvb
  left
  have hex : ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver v := by
    obtain ⟨P, hP, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S) v
    exact ⟨P, hP.isPrime, hPl⟩
  have hdef : v.ramificationIdxIn S = hex.choose.ramificationIdx R := by
    rw [Ideal.ramificationIdxIn, dif_pos hex]
  obtain ⟨hP, hPl⟩ := hex.choose_spec
  set P := hex.choose with hPdef
  have hepos : 0 < P.ramificationIdx R := Ideal.ramificationIdx_pos P R
  have he2 : 2 ≤ P.ramificationIdx R := by omega
  have hPbot : P ≠ ⊥ := by
    intro h
    apply hvb
    rw [hPl.over, h]
    simp [Ideal.under, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R S)]
  have hdvd : P ^ (P.ramificationIdx R) ∣ v.map (algebraMap R S) := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx v P hvb]
    exact Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx'
  have := pow_sub_one_dvd_differentIdeal R (p := v) P _ hvb hdvd
  have hP1 : P ∣ differentIdeal R S :=
    (dvd_pow_self P (by omega)).trans this
  refine ⟨P, ?_, hPl.over.symm⟩
  simp only [T, Multiset.mem_toFinset, Finset.mem_coe]
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hD).mpr
    ⟨(Ideal.prime_of_isPrime hPbot hP).irreducible, normalize_eq P, hP1⟩

end Ramified

end AffOrbicurve
