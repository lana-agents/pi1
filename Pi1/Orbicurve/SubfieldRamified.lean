module

public import Pi1.Orbicurve.SubfieldGalois
public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Finitely many primes ramify in an extension of coordinate rings

For `K₀ ⊆ F ⊆ N ⊆ Ω` (finite over `K₀ = k(t)`, characteristic `0`), only finitely many maximal
ideals of `coordRing k t F` ramify in `coordRing k t N` (`finite_ramified`): a ramified prime
divides the different ideal, which is nonzero.
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω) [CharZero k]
  (ht : Transcendental k t)

section

variable {F N : IntermediateField (K₀ k t) Ω} (hFN : F ≤ N) [FiniteDimensional (K₀ k t) N]

include ht in
set_option maxHeartbeats 1000000 in
/-- **Only finitely many maximal ideals ramify** in `coordRing k t N / coordRing k t F`. -/
theorem finite_ramified :
    {v : Ideal (coordRing k t F) | v.IsMaximal ∧
      (letI := algRing t hFN; v.ramificationIdxIn (coordRing k t N)) ≠ 1}.Finite := by
  classical
  letI iR := algRing t hFN
  letI : SMul (coordRing k t F) (coordRing k t N) := iR.toSMul
  letI : Module (coordRing k t F) (coordRing k t N) := iR.toModule
  letI := algFN t hFN
  haveI : FiniteDimensional (K₀ k t) F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFN).toLinearMap
      (IntermediateField.inclusion hFN).injective
  haveI : CharZero (K₀ k t) := charZero_of_injective_algebraMap (algebraMap k (K₀ k t)).injective
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  haveI : Algebra.IsSeparable (K₀ k t) N := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable (K₀ k t) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsScalarTower (K₀ k t) F N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional F N := FiniteDimensional.right (K₀ k t) F N
  haveI : Algebra.IsSeparable F N := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsScalarTower (coordRing k t F) (coordRing k t N) N := ⟨fun a b c => by
    change ((ringMap t hFN a * b : coordRing k t N) : N) * c =
      (IntermediateField.inclusion hFN (a : F)) * ((b : N) * c)
    rw [← mul_assoc]; rfl⟩
  haveI := isFractionRing_coordRing t F
  haveI := isFractionRing_coordRing t N
  haveI := isDedekindDomain_ring t ht F
  haveI := isDedekindDomain_ring t ht N
  haveI := module_finite_ringMap t ht hFN
  haveI : Module.IsTorsionFree (coordRing k t F) (coordRing k t N) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact ringMap_injective t hFN
  haveI : FaithfulSMul (coordRing k t F) (coordRing k t N) := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact ringMap_injective t hFN
  haveI : Algebra.IsIntegral (coordRing k t F) (coordRing k t N) := ⟨ringMap_isIntegral t hFN⟩
  haveI : IsIntegralClosure (coordRing k t N) (coordRing k t F) N := by
    refine ⟨Subtype.val_injective, fun {x} => ⟨fun hx => ?_, ?_⟩⟩
    · -- integral over `coordRing k t F`, hence over `k[t]`
      have hx' : IsIntegral (A₀ k t) x := by
        haveI : IsScalarTower (A₀ k t) (coordRing k t F) N :=
          IsScalarTower.of_algebraMap_eq fun _ => rfl
        haveI : Algebra.IsIntegral (A₀ k t) (coordRing k t F) :=
          ⟨fun b => integralClosure.isIntegral b⟩
        exact isIntegral_trans (R := A₀ k t) x hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact (Algebra.IsIntegral.isIntegral b).algebraMap
  set D := differentIdeal (coordRing k t F) (coordRing k t N)
  have hD : D ≠ ⊥ := by
    rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := N),
      coeIdeal_differentIdeal (coordRing k t F) F N]
    simp
  let T : Finset (Ideal (coordRing k t N)) :=
    (UniqueFactorizationMonoid.normalizedFactors D).toFinset
  refine ((T.finite_toSet.image
    (fun P => P.comap (algebraMap (coordRing k t F) (coordRing k t N)))).union
    (Set.finite_singleton (⊥ : Ideal (coordRing k t F)))).subset ?_
  rintro v ⟨hv, hne⟩
  by_cases hvb : v = ⊥
  · exact Or.inr hvb
  left
  have hex : ∃ P : Ideal (coordRing k t N), P.IsPrime ∧ P.LiesOver v := by
    obtain ⟨P, hP, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := coordRing k t N) v
    exact ⟨P, hP.isPrime, hPl⟩
  have hdef : v.ramificationIdxIn (coordRing k t N) =
      hex.choose.ramificationIdx (coordRing k t F) := by
    rw [Ideal.ramificationIdxIn, dif_pos hex]
  obtain ⟨hP, hPl⟩ := hex.choose_spec
  set P := hex.choose
  have hepos : 0 < P.ramificationIdx (coordRing k t F) := Ideal.ramificationIdx_pos P _
  have he2 : 2 ≤ P.ramificationIdx (coordRing k t F) := by omega
  have hPbot : P ≠ ⊥ := by
    intro h
    apply hvb
    rw [hPl.over, h]
    simp [Ideal.under]
  have hdvd : P ^ (P.ramificationIdx (coordRing k t F)) ∣
      v.map (algebraMap (coordRing k t F) (coordRing k t N)) := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx v P hvb]
    exact Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx'
  have := pow_sub_one_dvd_differentIdeal_aux (coordRing k t F) F N (p := v) P
    (by omega) hvb hdvd
  have hP1 : P ∣ D := (dvd_pow_self P (by omega)).trans this
  refine ⟨P, ?_, hPl.over.symm⟩
  simp only [T, Multiset.mem_toFinset, Finset.mem_coe]
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hD).mpr
    ⟨(Ideal.prime_of_isPrime hPbot hP).irreducible, normalize_eq P, hP1⟩

end

end AffOrbicurve
