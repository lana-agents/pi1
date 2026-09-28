module

public import Pi1.Orbicurve.Iso
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# A criterion for cores

Let `k` be a field of characteristic `0`, `X`, `H` affine orbicurves over `k` and `π : X → H` a
finite étale morphism. If every finite étale cover `Z → X` admits **at most one** finite étale
morphism `Z → H`, then `H` is the `k`-core of `X` (`AffOrbicurve.isCoreOf_of_subsingleton`).

Indeed, let `Y ∈ \overline{Loc}_k(X)`, with finite étale `Z → X`, `ψ : Z → Y`. Morphisms
`Y → H` are unique since `ψ` is dominant. For the existence, let `τ ∈ A_Z` be the coordinate of
`Z → X → H`. Represent `Y` (via a Noether normalization of its coordinate ring,
`AffOrbicurve.exists_integral_param`) and `Z` as normalizations of a line in subfields
`L_Y ⊆ L_Z` of an algebraically closed field `Ω` (`Pi1.Orbicurve.Embed`). For every
`σ ∈ Aut(Ω / L_Y)`, a component `V` of `Z ×_Y Z^σ` (`AffOrbicurve.exists_pullback_subfield`) is a
finite étale cover of `X` with two morphisms `V → H`, of coordinates `τ` and `σ(τ)`; so
`σ(τ) = τ`, whence `τ ∈ L_Y` and `τ ∈ A_Y`, and `τ` defines a finite étale morphism `Y → H`.
-/

@[expose] public section

universe u

open Ideal Polynomial IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace AffOrbicurve

variable {k : Type u} [Field k]

section Param

/-- In a one-dimensional domain, a finite injective extension of a polynomial ring in `s`
variables has `s ≤ 1`. -/
lemma le_one_of_integral_mvPolynomial {R : Type*} [CommRing R] [IsDomain R] [Algebra k R]
    [Ring.DimensionLEOne R] {s : ℕ} (g : MvPolynomial (Fin s) k →ₐ[k] R)
    (hinj : Function.Injective g) (hint : g.toRingHom.IsIntegral) : s ≤ 1 := by
  by_contra hs
  have hs : 1 < s := not_le.mp hs
  letI : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) R := ⟨hint⟩
  let i0 : Fin s := ⟨0, by omega⟩
  let i1 : Fin s := ⟨1, hs⟩
  have hi : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  -- `p₁ = (X₀)`, `p₂ = (X₀, X₁)` as kernels of substitutions
  let e1 : MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
    MvPolynomial.aeval fun i => if i = i0 then 0 else MvPolynomial.X i
  let e2 : MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
    MvPolynomial.aeval fun i => if i = i0 ∨ i = i1 then 0 else MvPolynomial.X i
  let p1 : Ideal (MvPolynomial (Fin s) k) := RingHom.ker e1.toRingHom
  let p2 : Ideal (MvPolynomial (Fin s) k) := RingHom.ker e2.toRingHom
  haveI : p1.IsPrime := RingHom.ker_isPrime _
  haveI : p2.IsPrime := RingHom.ker_isPrime _
  have he : e2 = e2.comp e1 := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [e1, e2, AlgHom.comp_apply, MvPolynomial.aeval_X]
    by_cases h0 : i = i0
    · simp [h0]
    · simp only [h0, if_false, false_or, MvPolynomial.aeval_X]
  have hp12 : p1 ≤ p2 := by
    intro x hx
    change e2 x = 0
    rw [he, AlgHom.comp_apply]
    change e1 x = 0 at hx
    rw [hx, map_zero]
  have hX0 : MvPolynomial.X i0 ∈ p1 := by
    change e1 (MvPolynomial.X i0) = 0
    simp [e1]
  have hX1 : MvPolynomial.X i1 ∈ p2 := by
    change e2 (MvPolynomial.X i1) = 0
    simp [e2]
  have hX1' : MvPolynomial.X i1 ∉ p1 := by
    change ¬ e1 (MvPolynomial.X i1) = 0
    simp [e1, hi.symm, MvPolynomial.X_ne_zero]
  have hp1 : p1 ≠ ⊥ := fun h => MvPolynomial.X_ne_zero (R := k) i0 (by
    rw [← Ideal.mem_bot, ← h]; exact hX0)
  -- lying over and going up
  have hbot : (⊥ : Ideal R).comap (algebraMap (MvPolynomial (Fin s) k) R) ≤ p1 := by
    intro x hx
    have : g x = 0 := hx
    rw [show x = 0 from hinj (this.trans (map_zero g).symm)]
    exact zero_mem _
  haveI : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  obtain ⟨Q1, -, hQ1, hQ1c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p1 ⊥ hbot
  have hQ1c' : Q1.comap (algebraMap (MvPolynomial (Fin s) k) R) ≤ p2 := hQ1c ▸ hp12
  obtain ⟨Q2, hQ12, hQ2, hQ2c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p2 Q1 hQ1c'
  have hQ1ne : Q1 ≠ ⊥ := by
    rintro rfl
    apply hp1
    rw [← hQ1c]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun h => hinj (h.trans (map_zero g).symm), fun h => by rw [h, map_zero]⟩
  have hQ1m : Q1.IsMaximal := hQ1.isMaximal hQ1ne
  have hQ : Q1 = Q2 := hQ1m.eq_of_le hQ2.ne_top hQ12
  apply hX1'
  rw [← hQ1c, hQ, hQ2c]
  exact hX1

/-- **Noether normalization of an affine orbicurve**: its coordinate ring is finite over a
polynomial ring in one variable. -/
theorem exists_integral_param (Y : AffOrbicurve k) :
    ∃ g : k[X] →ₐ[k] Y.A, Function.Injective g ∧ g.toRingHom.IsIntegral := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k Y.A
  have hint : g.toRingHom.IsIntegral := hfin.to_isIntegral
  have hs1 : s ≤ 1 := le_one_of_integral_mvPolynomial g hinj hint
  rcases Nat.lt_or_ge s 1 with hs0 | hs1'
  · -- `s = 0`: `A_Y` would be a field
    exfalso
    obtain rfl : s = 0 := by omega
    letI : Algebra (MvPolynomial (Fin 0) k) Y.A := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin 0) k) Y.A := ⟨hint⟩
    have hF : IsField (MvPolynomial (Fin 0) k) :=
      MulEquiv.isField (Field.toIsField k)
        (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toMulEquiv
    exact Y.not_isField (isField_of_isIntegral_of_isField' hF)
  · obtain rfl : s = 1 := by omega
    let e : MvPolynomial (Fin 1) k ≃ₐ[k] k[X] := MvPolynomial.uniqueAlgEquiv k (Fin 1)
    refine ⟨g.comp e.symm.toAlgHom, hinj.comp e.symm.injective, ?_⟩
    have : (g.comp e.symm.toAlgHom).toRingHom = g.toRingHom.comp e.symm.toRingEquiv.toRingHom :=
      rfl
    rw [this]
    exact RingHom.IsIntegral.trans _ _
      (RingHom.IsIntegral.of_finite (RingHom.Finite.of_surjective _ e.symm.surjective)) hint

end Param

section Subfield

variable {Ω : Type u} [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)

include ht in
/-- The coordinate ring of the `t`-line itself is `k[t]`. -/
lemma bijective_algebraMap_coordRing_bot :
    Function.Bijective (algebraMap (A₀ k t) (coordRing k t (⊥ : IntermediateField (K₀ k t) Ω))) := by
  refine ⟨fun a b h => Subtype.ext (congrArg (fun c : coordRing k t (⊥ : IntermediateField
    (K₀ k t) Ω) => ((c : (⊥ : IntermediateField (K₀ k t) Ω)) : Ω)) h), fun b => ?_⟩
  have hb : ((b : (⊥ : IntermediateField (K₀ k t) Ω)) : Ω) ∈
      (⊥ : IntermediateField (K₀ k t) Ω) := (b : (⊥ : IntermediateField (K₀ k t) Ω)).2
  obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp hb
  haveI := isPrincipalIdealRing_A₀ ht
  have hzint : IsIntegral (A₀ k t) z := by
    have h1 : IsIntegral (A₀ k t) ((b : (⊥ : IntermediateField (K₀ k t) Ω)) : Ω) := by
      haveI : IsScalarTower (A₀ k t) (⊥ : IntermediateField (K₀ k t) Ω) Ω :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      have := b.2
      rw [mem_integralClosure_iff] at this
      exact (isIntegral_algebraMap_iff (A := (⊥ : IntermediateField (K₀ k t) Ω)) (B := Ω)
        (algebraMap (⊥ : IntermediateField (K₀ k t) Ω) Ω).injective).mpr this
    rw [← hz] at h1
    haveI : IsScalarTower (A₀ k t) (K₀ k t) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact (isIntegral_algebraMap_iff (algebraMap (K₀ k t) Ω).injective).mp h1
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A₀ k t) (K := K₀ k t)).mp hzint
  refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
  rw [← hz, ← ha]
  rfl

/-- `k[X] ≅ k[t] = ` the coordinate ring of the `t`-line. -/
noncomputable def coordRingBotEquiv :
    k[X] ≃ₐ[k] coordRing k t (⊥ : IntermediateField (K₀ k t) Ω) :=
  (Polynomial.algEquivOfTranscendental k t ht).trans
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom k (A₀ k t) _)
      (bijective_algebraMap_coordRing_bot ht))

lemma coe_coordRingBotEquiv (p : k[X]) :
    (((coordRingBotEquiv ht p : coordRing k t (⊥ : IntermediateField (K₀ k t) Ω)) :
      (⊥ : IntermediateField (K₀ k t) Ω)) : Ω) = aeval t p := by
  change ((Polynomial.algEquivOfTranscendental k t ht p : A₀ k t) : Ω) = _
  change ((aeval (⟨t, Algebra.self_mem_adjoin_singleton k t⟩ : A₀ k t) p : A₀ k t) : Ω) = _
  rw [← Subalgebra.aeval_coe]

variable (L : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) L]
  [Algebra.IsSeparable (K₀ k t) L]

/-- **An affine orbicurve transported to a subfield orbicurve** along an isomorphism of its
coordinate ring with the coordinate ring of the normalization of the `t`-line in `L`. -/
noncomputable def ofEquiv (Z : AffOrbicurve k) (ψ : Z.A ≃ₐ[k] coordRing k t L) : AffOrbicurve k :=
  ofSubfield t ht L (fun w => Z.mult (w.comap ψ))
    (fun w hw => Z.mult_pos _ (Ideal.comap_isMaximal_of_surjective ψ ψ.surjective))
    (by
      refine (Z.finite_mult.image fun v => v.comap ψ.symm).subset ?_
      rintro w ⟨hw, hne⟩
      refine ⟨w.comap ψ, ⟨Ideal.comap_isMaximal_of_surjective ψ ψ.surjective, hne⟩, ?_⟩
      ext x
      simp only [Ideal.mem_comap]
      rw [AlgEquiv.apply_symm_apply])

lemma ofEquiv_A (Z : AffOrbicurve k) (ψ : Z.A ≃ₐ[k] coordRing k t L) :
    (ofEquiv ht L Z ψ).A = coordRing k t L := rfl

/-- The isomorphism `ofEquiv Z ψ ≅ Z`; its morphism `ofEquiv Z ψ → Z` has ring map `ψ`. -/
noncomputable def isoOfEquiv (Z : AffOrbicurve k) (ψ : Z.A ≃ₐ[k] coordRing k t L) :
    Iso (ofEquiv ht L Z ψ) Z :=
  Iso.ofAlgEquiv (X := ofEquiv ht L Z ψ) (Y := Z) ψ.symm (fun w _ => by
    exact congrArg Z.mult (comap_comap_symm ψ.toRingEquiv w).symm)

lemma isoOfEquiv_hom_f (Z : AffOrbicurve k) (ψ : Z.A ≃ₐ[k] coordRing k t L) (z : Z.A) :
    (isoOfEquiv ht L Z ψ).hom.f z = ψ z := rfl

lemma isoOfEquiv_inv_f (Z : AffOrbicurve k) (ψ : Z.A ≃ₐ[k] coordRing k t L)
    (x : coordRing k t L) : (isoOfEquiv ht L Z ψ).inv.f x = ψ.symm x := rfl

end Subfield

section Omega

variable (k)

/-- An algebraically closed field containing `k(t)`, algebraic over it. -/
abbrev ΩR : Type u := AlgebraicClosure (RatFunc k)

/-- The transcendental `t = X ∈ k(X) ⊆ Ω`. -/
noncomputable def tR : ΩR k := algebraMap (RatFunc k) (ΩR k) RatFunc.X

lemma transcendental_tR : Transcendental k (tR k) := by
  unfold tR
  rw [transcendental_algebraMap_iff (algebraMap (RatFunc k) (ΩR k)).injective]
  exact RatFunc.transcendental_X

lemma algebraMap_mem_K₀ (f : RatFunc k) : algebraMap (RatFunc k) (ΩR k) f ∈ K₀ k (tR k) := by
  have h : (k⟮RatFunc.X⟯ : IntermediateField k (RatFunc k)).map
      (IsScalarTower.toAlgHom k (RatFunc k) (ΩR k)) = K₀ k (tR k) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  rw [← h, RatFunc.adjoin_X]
  exact ⟨f, trivial, rfl⟩

instance isAlgebraic_K₀_ΩR : Algebra.IsAlgebraic (K₀ k (tR k)) (ΩR k) := by
  letI : Algebra (RatFunc k) (K₀ k (tR k)) :=
    ((algebraMap (RatFunc k) (ΩR k)).codRestrict (K₀ k (tR k)).toSubfield
      (algebraMap_mem_K₀ k)).toAlgebra
  haveI : IsScalarTower (RatFunc k) (K₀ k (tR k)) (ΩR k) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨fun z => (Algebra.IsAlgebraic.isAlgebraic (R := RatFunc k) z).extendScalars
    (fun a b h => (algebraMap (RatFunc k) (ΩR k)).injective (congrArg Subtype.val h))⟩

instance isAlgClosure_K₀_ΩR : IsAlgClosure (K₀ k (tR k)) (ΩR k) := ⟨inferInstance, inferInstance⟩

instance isGalois_K₀_ΩR [CharZero k] : IsGalois (K₀ k (tR k)) (ΩR k) where
  to_isSeparable := by
    haveI : CharZero (K₀ k (tR k)) :=
      charZero_of_injective_algebraMap (algebraMap k (K₀ k (tR k))).injective
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  to_normal := inferInstance

end Omega

section Conj

variable {Ω : Type u} [Field Ω] [Algebra k Ω] {t : Ω}

/-- The isomorphism of coordinate rings `coordRing L ≅ coordRing σ(L)` induced by an automorphism
`σ` of `Ω` over `k(t)`. -/
noncomputable def coordRingMapEquiv (σ : Ω ≃ₐ[K₀ k t] Ω) (L : IntermediateField (K₀ k t) Ω) :
    coordRing k t L ≃ₐ[k] coordRing k t (L.map σ.toAlgHom) :=
  AlgEquiv.ofRingEquiv (f := integralClosureEquiv (RingEquiv.refl (A₀ k t))
      (L.equivMap σ.toAlgHom).toRingEquiv (fun r => Subtype.ext (by
        change σ (algebraMap (K₀ k t) Ω (algebraMap (A₀ k t) (K₀ k t) r)) = _
        rw [AlgEquiv.commutes]; rfl)))
    (fun c => Subtype.ext (Subtype.ext (by
      change σ (algebraMap (K₀ k t) Ω (algebraMap k (K₀ k t) c)) = _
      rw [AlgEquiv.commutes]; rfl)))

@[simp] lemma coe_coordRingMapEquiv (σ : Ω ≃ₐ[K₀ k t] Ω) (L : IntermediateField (K₀ k t) Ω)
    (x : coordRing k t L) :
    (((coordRingMapEquiv σ L x : coordRing k t (L.map σ.toAlgHom)) : L.map σ.toAlgHom) : Ω) =
      σ ((x : L) : Ω) := rfl

end Conj

section Criterion

variable [CharZero k]

set_option maxHeartbeats 2000000 in
/-- **The key step of the criterion**: if every finite étale cover of `X` admits at most one
morphism to `H`, then for finite étale `φ : Z → X` and `ψ : Z → Y`, the ring map of `Z → X → H`
factors through `ψ`. -/
theorem mem_range_of_subsingleton {X H Y Z : AffOrbicurve k} (π : Hom X H)
    (h : ∀ V : AffOrbicurve k, Hom V X → Subsingleton (Hom V H))
    (φ : Hom Z X) (ψ : Hom Z Y) (a : H.A) : (φ.comp π).f a ∈ ψ.f.range := by
  classical
  have ht := transcendental_tR k
  haveI : CharZero (K₀ k (tR k)) :=
    charZero_of_injective_algebraMap (algebraMap k (K₀ k (tR k))).injective
  -- `Y` as a subfield orbicurve
  obtain ⟨g, hg, hgi⟩ := exists_integral_param Y
  let g' : coordRing k (tR k) (⊥ : IntermediateField (K₀ k (tR k)) (ΩR k)) →ₐ[k] Y.A :=
    g.comp (coordRingBotEquiv ht).symm.toAlgHom
  have hg' : Function.Injective g' := hg.comp (coordRingBotEquiv ht).symm.injective
  have hg'i : g'.toRingHom.IsIntegral := by
    have : g'.toRingHom = g.toRingHom.comp (coordRingBotEquiv ht).symm.toRingEquiv.toRingHom :=
      rfl
    rw [this]
    exact RingHom.IsIntegral.trans _ _ (RingHom.IsIntegral.of_finite
      (RingHom.Finite.of_surjective _ (coordRingBotEquiv ht).symm.surjective)) hgi
  obtain ⟨LY, _, -, ψY, -⟩ := exists_algEquiv_coordRing (tR k) Y.A g' hg' hg'i
  haveI : Algebra.IsSeparable (K₀ k (tR k)) LY := Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- `Z` as a subfield orbicurve over `LY`
  have hZi : (ψ.f.comp ψY.symm.toAlgHom).toRingHom.IsIntegral := by
    have : (ψ.f.comp ψY.symm.toAlgHom).toRingHom =
        ψ.f.toRingHom.comp ψY.symm.toRingEquiv.toRingHom := rfl
    rw [this]
    exact RingHom.IsIntegral.trans _ _ (RingHom.IsIntegral.of_finite
      (RingHom.Finite.of_surjective _ ψY.symm.surjective)) ψ.isIntegral
  obtain ⟨LZ, _, hYZ, ψZ, hψZ⟩ := exists_algEquiv_coordRing (tR k) Z.A
    (ψ.f.comp ψY.symm.toAlgHom) (ψ.injective.comp ψY.symm.injective) hZi
  haveI : Algebra.IsSeparable (K₀ k (tR k)) LZ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let Y' := ofEquiv ht LY Y ψY
  let Z' := ofEquiv ht LZ Z ψZ
  let eY := isoOfEquiv ht LY Y ψY
  let eZ := isoOfEquiv ht LZ Z ψZ
  let χ : Hom Z' Y' := eZ.hom.comp (ψ.comp eY.inv)
  have hχ : χ.f = ringMap (tR k) hYZ := AlgHom.ext fun b => hψZ b
  have hA : ∀ w : Ideal (coordRing k (tR k) LZ), w.IsMaximal →
      (letI := algRing (tR k) hYZ; w.ramificationIdx (coordRing k (tR k) LY)) * Z'.mult w =
        Y'.mult (w.comap (ringMap (tR k) hYZ)) := by
    intro w hw
    have := χ.etale w hw
    rw [hχ] at this
    exact this
  set τ : Z.A := (φ.comp π).f a with hτ
  -- `σ(τ) = τ` for every `σ ∈ Aut(Ω / LY)`
  have hfix : ∀ σ ∈ LY.fixingSubgroup, σ (((ψZ τ : coordRing k (tR k) LZ) : LZ) : ΩR k) =
      (((ψZ τ : coordRing k (tR k) LZ) : LZ) : ΩR k) := by
    intro σ hσ
    let LZσ : IntermediateField (K₀ k (tR k)) (ΩR k) := LZ.map σ.toAlgHom
    haveI : FiniteDimensional (K₀ k (tR k)) LZσ :=
      LinearEquiv.finiteDimensional (LZ.equivMap σ.toAlgHom).toLinearEquiv
    haveI : Algebra.IsSeparable (K₀ k (tR k)) LZσ :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    have hσY : ∀ x ∈ LY, σ x = x := (IntermediateField.mem_fixingSubgroup_iff LY σ).mp hσ
    have hYσ : LY ≤ LZσ := fun x hx => ⟨x, hYZ hx, hσY x hx⟩
    let ρ : Z'.A ≃ₐ[k] coordRing k (tR k) LZσ := coordRingMapEquiv σ LZ
    let Zσ := ofEquiv ht LZσ Z' ρ
    let eσ := isoOfEquiv ht LZσ Z' ρ
    let χσ : Hom Zσ Y' := eσ.hom.comp χ
    have hχσ : χσ.f = ringMap (tR k) hYσ := by
      apply AlgHom.ext
      intro b
      have e1 : χσ.f b = coordRingMapEquiv σ LZ (χ.f b) := rfl
      rw [e1, hχ]
      apply Subtype.ext; apply Subtype.ext
      rw [coe_coordRingMapEquiv]
      exact hσY _ b.1.2
    have hZσ : ∀ w : Ideal (coordRing k (tR k) LZσ), w.IsMaximal →
        (letI := algRing (tR k) hYσ; w.ramificationIdx (coordRing k (tR k) LY)) * Zσ.mult w =
          Y'.mult (w.comap (ringMap (tR k) hYσ)) := by
      intro w hw
      have := χσ.etale w hw
      rw [hχσ] at this
      exact this
    obtain ⟨m, m_pos, m_fin, hmZ, hmA⟩ := exists_pullback_subfield (tR k) ht hYZ hYσ Y'.mult
      Y'.mult_pos Y'.finite_mult Z'.mult Zσ.mult hA hZσ
    haveI : FiniteDimensional (K₀ k (tR k)) ↥(LZσ ⊔ LZ) :=
      IntermediateField.finiteDimensional_sup LZσ LZ
    haveI : Algebra.IsSeparable (K₀ k (tR k)) ↥(LZσ ⊔ LZ) :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    let V := ofSubfield (tR k) ht (LZσ ⊔ LZ) m m_pos m_fin
    let p : Hom V Z := (homOfLE ht le_sup_right hmA).comp eZ.hom
    let q : Hom V Z := (homOfLE ht le_sup_left hmZ).comp (eσ.hom.comp eZ.hom)
    have heq : p.comp (φ.comp π) = q.comp (φ.comp π) := (h V (p.comp φ)).elim _ _
    have := congrArg (fun r : Hom V H =>
      (r.f a).1.1) heq
    exact this.symm
  -- hence `τ ∈ LY`, and `τ` comes from `Y`
  have hmem : (((ψZ τ : coordRing k (tR k) LZ) : LZ) : ΩR k) ∈ LY := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup LY, IntermediateField.mem_fixedField_iff]
    exact hfix
  let b : coordRing k (tR k) LY := ⟨⟨_, hmem⟩, mem_coordRing_of_isIntegral (tR k) hmem
    (isIntegral_of_mem_coordRing (tR k) (ψZ τ))⟩
  refine ⟨ψY.symm b, ψZ.injective ?_⟩
  change ψZ ((ψ.f.comp ψY.symm.toAlgHom) b) = ψZ τ
  rw [hψZ]
  rfl

/-- **Criterion for cores**: if `π : X → H` is finite étale and every finite étale cover of `X`
admits at most one finite étale morphism to `H`, then `H` is the `k`-core of `X`. -/
theorem isCoreOf_of_subsingleton {X H : AffOrbicurve k} (π : Hom X H)
    (h : ∀ Z : AffOrbicurve k, Hom Z X → Subsingleton (Hom Z H)) : IsCoreOf X H := by
  refine ⟨⟨X, ⟨Hom.id X⟩, ⟨π⟩⟩, fun Y hY => ?_⟩
  obtain ⟨Z, ⟨φ⟩, ⟨ψ⟩⟩ := hY
  refine ⟨?_, ⟨fun a b => Hom.ext ?_⟩⟩
  · -- existence: the ring map of `Z → X → H` factors through `ψ`
    have hr : ∀ c : H.A, (φ.comp π).f c ∈ ψ.f.range :=
      mem_range_of_subsingleton π h φ ψ
    let e := AlgEquiv.ofInjective ψ.f ψ.injective
    let f : H.A →ₐ[k] Y.A := e.symm.toAlgHom.comp ((φ.comp π).f.codRestrict ψ.f.range hr)
    have hf : ∀ c, ψ.f (f c) = (φ.comp π).f c := fun c => by
      have := e.apply_symm_apply ⟨_, hr c⟩
      exact congrArg Subtype.val this
    have hcomp : ψ.f.comp f = (φ.comp π).f := AlgHom.ext hf
    refine ⟨{ f := f, injective := ?_, isIntegral := ?_, etale := ?_ }⟩
    · intro c d hcd
      exact (φ.comp π).injective (by rw [← hf, ← hf, hcd])
    · intro y
      obtain ⟨p, hp, hpy⟩ := (φ.comp π).isIntegral (ψ.f y)
      refine ⟨p, hp, ψ.injective ?_⟩
      rw [map_zero]
      have := Polynomial.hom_eval₂ p f.toRingHom ψ.f.toRingHom y
      have hc : ψ.f.toRingHom.comp f.toRingHom = (φ.comp π).f.toRingHom :=
        congrArg AlgHom.toRingHom hcomp
      change ψ.f.toRingHom (Polynomial.eval₂ f.toRingHom y p) = 0
      rw [this, hc]
      exact hpy
    · intro w hw
      letI : Algebra Y.A Z.A := ψ.f.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral Y.A Z.A := ⟨ψ.isIntegral⟩
      have hker : RingHom.ker (algebraMap Y.A Z.A) ≤ w := by
        intro x hx
        have : ψ.f x = 0 := hx
        rw [show x = 0 from ψ.injective (this.trans (map_zero _).symm)]
        exact zero_mem _
      obtain ⟨z, hz, hzw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral w hker
      have h1 := (φ.comp π).etale z hz
      have h2 := ψ.etale z hz
      have h3 := ramificationIdx_comp f.toRingHom ψ.f.toRingHom ψ.injective z
      have hc : ψ.f.toRingHom.comp f.toRingHom = (φ.comp π).f.toRingHom :=
        congrArg AlgHom.toRingHom hcomp
      rw [hc] at h3
      have hzw' : z.comap ψ.f.toRingHom = w := hzw
      have hzw'' : z.comap ψ.f = w := hzw
      rw [hzw'] at h3
      rw [hzw''] at h2
      have hv : z.comap (φ.comp π).f = w.comap f := by
        rw [← hzw'', ← hcomp]
        rfl
      rw [hv, h3, mul_assoc, h2] at h1
      exact h1
  · -- uniqueness: `ψ` is dominant
    have := (h Z φ).elim (ψ.comp a) (ψ.comp b)
    apply AlgHom.ext
    intro c
    exact ψ.injective (congrArg (fun r : Hom Z H => r.f c) this)

end Criterion

end AffOrbicurve
