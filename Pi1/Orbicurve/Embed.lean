/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbicurve.SubfieldGalois

/-!
# Embedding covers of subfield orbicurves into `Ω`

Let `Ω` be algebraically closed and `B` a finite extension of `K₀ = k(t)` inside `Ω`. Every
domain `Z` finite type over `k`, integrally closed, and integral over the coordinate ring of `B`
(e.g. the coordinate ring of a finite étale cover of `ofSubfield B m`) is the coordinate ring of a
finite extension `L ⊇ B` inside `Ω` (`exists_algEquiv_coordRing`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

section Embed

variable [IsAlgClosed Ω] {B : IntermediateField (K₀ k t) Ω} [FiniteDimensional (K₀ k t) B]
  (Z : Type u) [CommRing Z] [IsDomain Z] [Algebra k Z] [IsIntegrallyClosed Z]
  [Algebra.FiniteType k Z]

/-- The inclusion of the coordinate ring of `B` into `Ω`. -/
noncomputable def coordRingVal : coordRing k t B →+* Ω :=
  B.val.toRingHom.comp (coordRing k t B).val.toRingHom

omit [IsAlgClosed Ω] [FiniteDimensional (K₀ k t) B] in
lemma coordRingVal_injective : Function.Injective (coordRingVal t (B := B)) :=
  fun _ _ h => Subtype.val_injective (Subtype.val_injective h)

omit [IsAlgClosed Ω] [FiniteDimensional (K₀ k t) B] in
lemma isIntegral_A₀_of_coordRing {x : Ω} (h : IsIntegral (coordRing k t B) x) :
    IsIntegral (A₀ k t) x := by
  haveI : IsScalarTower (A₀ k t) (coordRing k t B) Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact isIntegral_trans (R := A₀ k t) (A := coordRing k t B) _ h

omit [IsAlgClosed Ω] [FiniteDimensional (K₀ k t) B] in
lemma mem_coordRing_of_isIntegral {L : IntermediateField (K₀ k t) Ω} {x : Ω} (hx : x ∈ L)
    (h : IsIntegral (A₀ k t) x) : (⟨x, hx⟩ : L) ∈ coordRing k t L := by
  haveI : IsScalarTower (A₀ k t) L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [mem_integralClosure_iff]
  exact (isIntegral_algebraMap_iff (A := L) (B := Ω) (algebraMap L Ω).injective).mp h

omit [IsAlgClosed Ω] [FiniteDimensional (K₀ k t) B] in
lemma isIntegral_of_mem_coordRing {L : IntermediateField (K₀ k t) Ω}
    (x : coordRing k t L) : IsIntegral (A₀ k t) ((x : L) : Ω) := by
  haveI : IsScalarTower (A₀ k t) L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := x.2
  rw [mem_integralClosure_iff] at this
  exact (isIntegral_algebraMap_iff (A := L) (B := Ω) (algebraMap L Ω).injective).mpr this

set_option maxHeartbeats 1000000 in
theorem exists_algEquiv_coordRing (g : coordRing k t B →ₐ[k] Z) (hg : Function.Injective g)
    (hgi : g.toRingHom.IsIntegral) :
    ∃ (L : IntermediateField (K₀ k t) Ω) (_ : FiniteDimensional (K₀ k t) L) (hBL : B ≤ L)
      (ψ : Z ≃ₐ[k] coordRing k t L), ∀ b, ψ (g b) = ringMap t hBL b := by
  classical
  letI : Algebra (coordRing k t B) Z := g.toRingHom.toAlgebra
  have hval : algebraMap (coordRing k t B) Ω = coordRingVal t := rfl
  haveI : Module.IsTorsionFree (coordRing k t B) Z := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hg
  haveI : Module.IsTorsionFree (coordRing k t B) Ω := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, hval]; exact coordRingVal_injective t
  haveI : Algebra.IsIntegral (coordRing k t B) Z := ⟨hgi⟩
  haveI : Algebra.IsAlgebraic (coordRing k t B) Z := Algebra.IsIntegral.isAlgebraic
  let ι : Z →ₐ[coordRing k t B] Ω := IsAlgClosed.lift
  have hιg : ∀ b, ι (g b) = coordRingVal t b := fun b => (ι.commutes b).trans (by rw [hval])
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hker : RingHom.ker ι.toRingHom = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := coordRing k t B)
      ext b
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      change ι (g b) = 0 ↔ b = 0
      rw [hιg, map_eq_zero_iff _ (coordRingVal_injective t)]
    have : a ∈ RingHom.ker ι.toRingHom := ha
    rwa [hker] at this
  have hιk : ∀ c : k, ι (algebraMap k Z c) = algebraMap k Ω c := by
    intro c
    rw [← g.commutes c, hιg]; rfl
  have hA₀ : ∀ a : A₀ k t, ∃ z : Z, ι z = (a : Ω) := fun a =>
    ⟨g (algebraMap (A₀ k t) (coordRing k t B) a), by rw [hιg]; rfl⟩
  -- the fraction field of `Z`, embedded into `Ω`
  let K := FractionRing Z
  let ιK : K →+* Ω := IsFractionRing.lift (g := ι.toRingHom) hι
  have hιK : ∀ z : Z, ιK (algebraMap Z K z) = ι z := fun z => IsFractionRing.lift_algebraMap hι z
  let S : Subfield Ω := ιK.fieldRange
  have hιS : ∀ z : Z, ι z ∈ S := fun z => ⟨algebraMap Z K z, hιK z⟩
  let Sk : IntermediateField k Ω := S.toIntermediateField fun c => by
    rw [← hιk c]; exact hιS _
  have hK₀S : ∀ x : K₀ k t, (x : Ω) ∈ S := by
    have : K₀ k t ≤ Sk := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      obtain ⟨z, hz⟩ := hA₀ ⟨t, Algebra.self_mem_adjoin_singleton k t⟩
      change t ∈ S
      have : ι z = t := hz
      rw [← this]; exact hιS z
    exact fun x => this x.2
  let L : IntermediateField (K₀ k t) Ω := S.toIntermediateField fun x => hK₀S x
  have hmemL : ∀ {x : Ω}, x ∈ L ↔ ∃ a b : Z, ι b ≠ 0 ∧ x = ι a / ι b := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Z) y
      refine ⟨a, b, ?_, ?_⟩
      · rw [← hιK]; exact (map_ne_zero ιK).mpr
          ((map_ne_zero_iff _ (IsFractionRing.injective Z K)).mpr (nonZeroDivisors.ne_zero hb))
      · rw [map_div₀, hιK, hιK]
    · rintro ⟨a, b, -, rfl⟩
      exact div_mem (hιS a) (hιS b)
  -- `B ⊆ L`
  have hBL : B ≤ L := by
    intro x hx
    haveI := isFractionRing_coordRing t B
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := coordRing k t B) (⟨x, hx⟩ : B)
    have h2 : ((algebraMap (coordRing k t B) B a / algebraMap (coordRing k t B) B b : B) : Ω) = x :=
      congrArg Subtype.val hab
    have e : ∀ c : coordRing k t B, ((algebraMap (coordRing k t B) B c : B) : Ω) = ι (g c) := by
      intro c; rw [hιg]; rfl
    rw [← h2, IntermediateField.coe_div, e, e]
    exact div_mem (hιS _) (hιS _)
  -- integrality of the image of `Z`
  have hint : ∀ z : Z, IsIntegral (coordRing k t B) (ι z) := by
    intro z
    obtain ⟨p, hp, hpz⟩ := hgi z
    refine ⟨p, hp, ?_⟩
    have hcomp : algebraMap (coordRing k t B) Ω = ι.toRingHom.comp g.toRingHom :=
      RingHom.ext fun b => by rw [hval]; exact (hιg b).symm
    rw [hcomp]
    have := Polynomial.hom_eval₂ p g.toRingHom (ι.toRingHom : Z →+* Ω) z
    rw [hpz, map_zero] at this
    exact this.symm
  have hintA₀ : ∀ z : Z, IsIntegral (A₀ k t) (ι z) := by
    intro z
    exact isIntegral_A₀_of_coordRing t (hint z)
  have hintK₀ : ∀ z : Z, IsIntegral (K₀ k t) (ι z) := fun z =>
    (hintA₀ z).tower_top (A := K₀ k t)
  -- `L` is finite over `K₀`
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k Z).FG)
  let L₀ : IntermediateField (K₀ k t) Ω := IntermediateField.adjoin (K₀ k t) (ι '' (s : Set Z))
  haveI : Finite (ι '' (s : Set Z)) := (s.finite_toSet.image _).to_subtype
  haveI : FiniteDimensional (K₀ k t) L₀ :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨z, -, rfl⟩; exact hintK₀ z)
  have hιL₀ : ∀ z : Z, ι z ∈ L₀ := by
    let S' : Subalgebra k Z :=
      { carrier := {z | ι z ∈ L₀}
        mul_mem' := fun ha hb => by simp only [Set.mem_setOf_eq, map_mul] at *; exact mul_mem ha hb
        add_mem' := fun ha hb => by simp only [Set.mem_setOf_eq, map_add] at *; exact add_mem ha hb
        algebraMap_mem' := fun c => by
          simp only [Set.mem_setOf_eq]
          rw [hιk, IsScalarTower.algebraMap_apply k (K₀ k t) Ω]
          exact L₀.algebraMap_mem _ }
    have : (⊤ : Subalgebra k Z) ≤ S' := by
      rw [← hs, Algebra.adjoin_le_iff]
      intro z hz
      exact IntermediateField.subset_adjoin _ _ ⟨z, hz, rfl⟩
    exact fun z => this trivial
  have hLL₀ : L ≤ L₀ := by
    intro x hx
    obtain ⟨a, b, -, rfl⟩ := hmemL.mp hx
    exact div_mem (hιL₀ a) (hιL₀ b)
  haveI : FiniteDimensional (K₀ k t) L :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hLL₀).toLinearMap
      (IntermediateField.inclusion hLL₀).injective
  -- the isomorphism `Z ≃ coordRing L`
  let ψ₀ : Z →ₐ[k] coordRing k t L :=
    { toFun := fun z => ⟨⟨ι z, hιS z⟩, mem_coordRing_of_isIntegral t (hιS z) (hintA₀ z)⟩
      map_one' := Subtype.ext (Subtype.ext (map_one ι))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (map_mul ι a b))
      map_zero' := Subtype.ext (Subtype.ext (map_zero ι))
      map_add' := fun a b => Subtype.ext (Subtype.ext (map_add ι a b))
      commutes' := fun c => Subtype.ext (Subtype.ext (hιk c)) }
  have hψ₀ : ∀ z, ((ψ₀ z : L) : Ω) = ι z := fun _ => rfl
  have hinj : Function.Injective ψ₀ := fun a b h => hι (by
    rw [← hψ₀, ← hψ₀, h])
  have hsurj : Function.Surjective ψ₀ := by
    intro x
    obtain ⟨y, hy⟩ : ((x : L) : Ω) ∈ S := (x : L).2
    obtain ⟨p, hp, hpx⟩ := isIntegral_of_mem_coordRing t x
    let φ₀ : A₀ k t →+* Z := g.toRingHom.comp (algebraMap (A₀ k t) (coordRing k t B))
    have hφ₀ : ιK.comp ((algebraMap Z K).comp φ₀) = algebraMap (A₀ k t) Ω := by
      ext a
      change ιK (algebraMap Z K (g _)) = _
      rw [hιK, hιg]; rfl
    have hyint : IsIntegral Z y := by
      refine ⟨p.map φ₀, hp.map _, ?_⟩
      apply ιK.injective
      rw [Polynomial.eval₂_map, Polynomial.hom_eval₂, hφ₀, map_zero, hy]
      exact hpx
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Z) (K := K)).mp hyint
    refine ⟨z, Subtype.ext (Subtype.ext ?_)⟩
    rw [hψ₀, ← hιK, hz, hy]
  let ψ : Z ≃ₐ[k] coordRing k t L := AlgEquiv.ofBijective ψ₀ ⟨hinj, hsurj⟩
  refine ⟨L, inferInstance, hBL, ψ, fun b => Subtype.ext (Subtype.ext ?_)⟩
  change ι (g b) = _
  rw [hιg]; rfl

end Embed

end AffOrbicurve
