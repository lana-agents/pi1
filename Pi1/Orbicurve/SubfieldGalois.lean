module

public import Pi1.Orbicurve.Subfield
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Ramification in Galois closures of subfields

Let `N ⊆ Ω` be a finite Galois extension of `K₀ = k(t)` and `G = Gal(N / K₀)`. For an intermediate
field `K₀ ⊆ F ⊆ N`, the subgroup `fixSub t N F = Gal(N / F)` of `G` is a Galois group of the
coordinate ring `coordRing k t N` over `coordRing k t F` (`isGaloisGroup_fixSub`). Consequently, for
`F ⊆ L ⊆ N` and a prime `u` of `coordRing k t N` over `w` in `coordRing k t L` and `v` in
`coordRing k t F` (residue fields of characteristic `0`),

  `e(u | v) = |I_u(N / F)|`, `e(u | w) = |I_u(N / F) ∩ Gal(N / L)|`,

so `e(w | v) = 1` if and only if the inertia group `I_u(N / F)` fixes `L`
(`ramificationIdx_eq_one_iff`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

section Galois

variable (N : IntermediateField (K₀ k t) Ω)

/-- The subgroup `Gal(N / F)` of `Gal(N / K₀)` (the elements fixing `F ∩ N`). -/
def fixSub (F : IntermediateField (K₀ k t) Ω) : Subgroup (N ≃ₐ[K₀ k t] N) where
  carrier := {σ | ∀ x : N, (x : Ω) ∈ F → σ x = x}
  one_mem' _ _ := rfl
  mul_mem' {σ τ} hσ hτ x hx := by
    rw [AlgEquiv.mul_apply, hτ x hx, hσ x hx]
  inv_mem' {σ} hσ x hx := by
    rw [← hσ x hx]
    conv_lhs => rw [← hσ x hx]
    simp

variable {N}

lemma mem_fixSub {F : IntermediateField (K₀ k t) Ω} {σ : N ≃ₐ[K₀ k t] N} :
    σ ∈ fixSub t N F ↔ ∀ x : N, (x : Ω) ∈ F → σ x = x := Iff.rfl

lemma fixSub_antitone {F L : IntermediateField (K₀ k t) Ω} (h : F ≤ L) :
    fixSub t N L ≤ fixSub t N F := fun _ hσ x hx => hσ x (h hx)

variable {F : IntermediateField (K₀ k t) Ω} (hFN : F ≤ N)

lemma fixSub_eq_fixingSubgroup :
    fixSub t N F = (IntermediateField.restrict hFN).fixingSubgroup := by
  ext σ
  rw [mem_fixSub, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    exact h x ((IntermediateField.mem_restrict hFN x).mp hx)
  · intro h x hx
    exact h x ((IntermediateField.mem_restrict hFN x).mpr hx)

/-- The algebra structure of `coordRing k t N` over `coordRing k t F`. -/
noncomputable abbrev algRing : Algebra (coordRing k t F) (coordRing k t N) :=
  (ringMap t hFN).toRingHom.toAlgebra

lemma module_finite_ringMap [FiniteDimensional (K₀ k t) N] [Algebra.IsSeparable (K₀ k t) N]
    (ht : Transcendental k t) (hFN : F ≤ N) :
    @Module.Finite (coordRing k t F) (coordRing k t N) _ _ (algRing t hFN).toModule := by
  letI iR := algRing t hFN
  letI : SMul (coordRing k t F) (coordRing k t N) := iR.toSMul
  letI : Module (coordRing k t F) (coordRing k t N) := iR.toModule
  haveI := finite_ring t ht N
  haveI : IsScalarTower (A₀ k t) (coordRing k t F) (coordRing k t N) :=
    ⟨fun a b c => by
      apply Subtype.ext; apply Subtype.ext
      change ((a : Ω) * (b : Ω)) * (c : Ω) = (a : Ω) * ((b : Ω) * (c : Ω))
      ring⟩
  exact Module.Finite.of_restrictScalars_finite (A₀ k t) _ _

/-- The inclusion `F → N` as an algebra structure. -/
noncomputable abbrev algFN : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra

lemma fixSub_eq_fixingSubgroup_range :
    letI := algFN t hFN
    fixSub t N F = _root_.fixingSubgroup (N ≃ₐ[K₀ k t] N) (Set.range (algebraMap F N)) := by
  letI := algFN t hFN
  ext σ
  rw [mem_fixSub, mem_fixingSubgroup_iff]
  constructor
  · rintro h _ ⟨x, rfl⟩
    exact h _ x.2
  · intro h x hx
    exact h x ⟨⟨x, hx⟩, rfl⟩

lemma isFractionRing_coordRing (L : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) L] :
    IsFractionRing (coordRing k t L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension (A₀ k t) (K₀ k t) L (coordRing k t L)

variable [FiniteDimensional (K₀ k t) N] [IsGalois (K₀ k t) N]

/-- **`Gal(N / F)` is a Galois group of `coordRing k t N` over `coordRing k t F`.** -/
theorem isGaloisGroup_fixSub (ht : Transcendental k t) :
    letI := algRing t hFN
    IsGaloisGroup (fixSub t N F) (coordRing k t F) (coordRing k t N) := by
  letI iR := algRing t hFN
  letI : SMul (coordRing k t F) (coordRing k t N) := iR.toSMul
  letI := algFN t hFN
  haveI : FiniteDimensional (K₀ k t) F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFN).toLinearMap
      (IntermediateField.inclusion hFN).injective
  haveI : IsScalarTower (coordRing k t F) (coordRing k t N) N := ⟨fun a b c => by
    change ((ringMap t hFN a * b : coordRing k t N) : N) * c =
      (IntermediateField.inclusion hFN (a : F)) * ((b : N) * c)
    rw [← mul_assoc]; rfl⟩
  haveI : IsScalarTower (K₀ k t) F N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := isFractionRing_coordRing t F
  haveI := isFractionRing_coordRing t N
  haveI : Algebra.IsSeparable (K₀ k t) F :=
    Algebra.IsSeparable.of_algHom (F := K₀ k t) (E := F) (E' := N) (IntermediateField.inclusion hFN)
  haveI := isDedekindDomain_ring t ht F
  haveI : Algebra.IsIntegral (coordRing k t F) (coordRing k t N) := ⟨ringMap_isIntegral t hFN⟩
  haveI hG : IsGaloisGroup (fixSub t N F) F N := by
    rw [fixSub_eq_fixingSubgroup_range t hFN]
    exact IsGaloisGroup.of_isScalarTower (N ≃ₐ[K₀ k t] N) (K₀ k t) N F
  exact IsGaloisGroup.of_isFractionRing (fixSub t N F) (coordRing k t F) (coordRing k t N) F N

section Ramification

variable [CharZero k] (ht : Transcendental k t)

include ht in
set_option maxHeartbeats 1000000 in
/-- **`e(u | v) = |I_u(N / F)|`**. -/
theorem ramificationIdx_eq_card_inertia (hFN : F ≤ N) (u : Ideal (coordRing k t N))
    [hu : u.IsMaximal] :
    letI := algRing t hFN
    u.ramificationIdx (coordRing k t F) =
      Nat.card ((u.inertia (N ≃ₐ[K₀ k t] N)) ⊓ fixSub t N F : Subgroup _) := by
  letI iR := algRing t hFN
  letI : SMul (coordRing k t F) (coordRing k t N) := iR.toSMul
  letI : Module (coordRing k t F) (coordRing k t N) := iR.toModule
  haveI : FiniteDimensional (K₀ k t) F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFN).toLinearMap
      (IntermediateField.inclusion hFN).injective
  haveI : Algebra.IsSeparable (K₀ k t) F :=
    Algebra.IsSeparable.of_algHom (F := K₀ k t) (E := F) (E' := N) (IntermediateField.inclusion hFN)
  haveI := isGaloisGroup_fixSub t hFN ht
  haveI := module_finite_ringMap t ht hFN
  haveI := isDedekindDomain_ring t ht F
  haveI := isDedekindDomain_ring t ht N
  haveI : Module.IsTorsionFree (coordRing k t F) (coordRing k t N) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact ringMap_injective t hFN
  haveI : Finite (fixSub t N F) := inferInstance
  let v := u.comap (algebraMap (coordRing k t F) (coordRing k t N))
  haveI : v.IsPrime := Ideal.comap_isPrime _ _
  haveI : u.LiesOver v := ⟨rfl⟩
  haveI : CharZero (coordRing k t F) :=
    charZero_of_injective_algebraMap (algebraMap k (coordRing k t F)).injective
  haveI : CharZero v.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap k v.ResidueField).injective
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v u (fixSub t N F),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := fixSub t N F) v u]
  change Nat.card (u.toAddSubgroup.inertia (fixSub t N F)) = _
  rw [← AddSubgroup.inertia_map_subtype,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

include ht in
/-- **Unramifiedness via inertia**: for `F ⊆ L ⊆ N` and a maximal ideal `u` of the coordinate ring
of `N`, `e(u ∩ L | u ∩ F) = 1` iff the inertia group `I_u(N / F)` fixes `L`. -/
theorem ramificationIdx_eq_one_iff {L : IntermediateField (K₀ k t) Ω} (hFL : F ≤ L) (hLN : L ≤ N)
    (u : Ideal (coordRing k t N)) [hu : u.IsMaximal] :
    (letI := algRing t hFL; (u.comap (ringMap t hLN)).ramificationIdx (coordRing k t F)) = 1 ↔
      ((u.inertia (N ≃ₐ[K₀ k t] N)) ⊓ fixSub t N F : Subgroup _) ≤ fixSub t N L := by
  have hFN := hFL.trans hLN
  have hcomp : (ringMap t hLN).toRingHom.comp (ringMap t hFL).toRingHom =
      (ringMap t hFN).toRingHom := RingHom.ext fun _ => rfl
  haveI : FiniteDimensional (K₀ k t) L :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hLN).toLinearMap
      (IntermediateField.inclusion hLN).injective
  haveI : Algebra.IsSeparable (K₀ k t) L :=
    Algebra.IsSeparable.of_algHom (F := K₀ k t) (E := L) (E' := N) (IntermediateField.inclusion hLN)
  haveI := isDedekindDomain_ring t ht L
  have htower := AffOrbicurve.ramificationIdx_comp (ringMap t hFL).toRingHom
    (ringMap t hLN).toRingHom (ringMap_injective t hLN) u
  rw [hcomp] at htower
  have hF := ramificationIdx_eq_card_inertia t ht hFN u
  have hL := ramificationIdx_eq_card_inertia t ht hLN u
  have hpos : 0 < (letI := algRing t hLN; u.ramificationIdx (coordRing k t L)) := by
    letI iR := algRing t hLN
    letI : Module (coordRing k t L) (coordRing k t N) := iR.toModule
    haveI := module_finite_ringMap t ht hLN
    exact Ideal.ramificationIdx_pos u _
  have hle : ((u.inertia (N ≃ₐ[K₀ k t] N)) ⊓ fixSub t N L : Subgroup _) ≤
      (u.inertia (N ≃ₐ[K₀ k t] N)) ⊓ fixSub t N F := inf_le_inf_left _ (fixSub_antitone t hFL)
  constructor
  · intro h1
    change (letI := algRing t hFL; (u.comap (ringMap t hLN).toRingHom).ramificationIdx
      (coordRing k t F)) = 1 at h1
    rw [h1, one_mul] at htower
    have hcard : Nat.card ((u.inertia (N ≃ₐ[K₀ k t] N)) ⊓ fixSub t N F : Subgroup _) =
        Nat.card ((u.inertia (N ≃ₐ[K₀ k t] N)) ⊓ fixSub t N L : Subgroup _) := by
      rw [← hF, ← hL]; exact htower
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard.le
    rw [← heq]
    exact inf_le_right
  · intro h
    have heq : ((u.inertia (N ≃ₐ[K₀ k t] N)) ⊓ fixSub t N F : Subgroup _) =
        (u.inertia (N ≃ₐ[K₀ k t] N)) ⊓ fixSub t N L :=
      le_antisymm (le_inf inf_le_left h) hle
    have : (letI := algRing t hFN; u.ramificationIdx (coordRing k t F)) =
        (letI := algRing t hLN; u.ramificationIdx (coordRing k t L)) := by
      rw [hF, hL, heq]
    rw [this] at htower
    have key : ∀ a b : ℕ, 0 < b → b = a * b → a = 1 := fun a b hb h =>
      Nat.eq_of_mul_eq_mul_right hb (by rw [one_mul]; exact h.symm)
    exact key _ _ hpos htower

end Ramification

end Galois

end AffOrbicurve
