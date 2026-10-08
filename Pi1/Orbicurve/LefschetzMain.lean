module

public import Pi1.Orbicurve.Descent
public import Pi1.Orbicurve.EmbedComplex
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.Polynomial.Subring

/-!
# [CanLift], Proposition 2.7 over any field of characteristic `0` from the case `k = ℂ`

`AffOrbicurve.canLift27_of_complex`: if for every elliptic curve `E / ℂ` with non-exceptional
`j`-invariant `(E ∖ {0}) / {±1}` is the `ℂ`-core of `E ∖ {0}`, then the same holds over every
field of characteristic `0` (`CanLift27.{0}`). The proof (Lefschetz principle):

* `CanLift27` is equivalent to `CoreStar` (uniqueness of morphisms from covers of `E ∖ {0}` to
  `(E ∖ {0}) / {±1}`, `isCoreOf_iff_coreStar`);
* `CoreStar` descends along field embeddings (`coreStar_of_map`), in particular from `ℂ` to any
  countable algebraically closed field (`nonempty_ringHom_complex`) and from `k̄` to `k`;
* over an algebraically closed field `K`, the data of a violation of `CoreStar` are defined over a
  countable algebraically closed subfield (`eq_of_descended`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial WeierstrassCurve

namespace AffOrbicurve

section JMap

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

/-- An embedding of `K(E_K)` restricts to an embedding of `k(E)` with the same coordinates. -/
lemma exists_j_of_map (E : WeierstrassCurve k) (E' : WeierstrassCurve K)
    (hE : E.map (algebraMap k K) = E') (j : E'.toAffine.FunctionField →ₐ[K] Ω) :
    ∃ j₀ : E.toAffine.FunctionField →ₐ[k] Ω, tE j₀ = tE j ∧ yE j₀ = yE j := by
  subst hE
  refine ⟨{ (j.toRingHom.comp (ffMap (algebraMap k K) E)) with
      commutes' := fun c => by
        change j (ffMap (algebraMap k K) E (algebraMap k _ c)) = algebraMap k Ω c
        rw [IsScalarTower.algebraMap_apply k K Ω]
        have : algebraMap k E.toAffine.FunctionField c =
            algebraMap E.toAffine.CoordinateRing _ (algebraMap k _ c) := rfl
        rw [this, ffMap_algebraMap]
        have h2 : Affine.CoordinateRing.map E.toAffine (algebraMap k K) (algebraMap k _ c) =
            algebraMap K (E.map (algebraMap k K)).toAffine.CoordinateRing (algebraMap k K c) := by
          change Affine.CoordinateRing.map E.toAffine (algebraMap k K)
            (Affine.CoordinateRing.mk _ (C (C c))) = _
          rw [Affine.CoordinateRing.map_mk]
          simp; rfl
        rw [h2, ← IsScalarTower.algebraMap_apply, AlgHom.commutes] }, ?_, ?_⟩
  · change j (ffMap (algebraMap k K) E (ellX E)) = _
    rw [ffMap_ellX]; rfl
  · change j (ffMap (algebraMap k K) E (ellY E)) = _
    rw [ffMap_ellY]; rfl

end JMap

section Countable

open Cardinal

/-- **Countable algebraically closed subfields**: every finite subset of an algebraically closed
field of characteristic `0` lies in a countable algebraically closed subfield. -/
lemma exists_algClosed_countable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Set K) (hS : S.Finite) :
    ∃ L₀ : Subfield K, IsAlgClosed L₀ ∧ Countable L₀ ∧ S ⊆ L₀ := by
  let F := Subfield.closure S
  have hF : #F ≤ ℵ₀ := by
    refine (Subfield.cardinalMk_closure_le_max S).trans (max_le ?_ le_rfl)
    exact le_of_lt (Cardinal.lt_aleph0_iff_set_finite.mpr hS)
  let A := algebraicClosure F K
  haveI : IsAlgClosed A := IsAlgClosure.isAlgClosed F
  have hA : #A ≤ ℵ₀ := (Algebra.IsAlgebraic.cardinalMk_le_max F A).trans (max_le hF le_rfl)
  refine ⟨A.toSubfield, inferInstanceAs (IsAlgClosed A), ?_, ?_⟩
  · have : Countable A := Cardinal.mk_le_aleph0_iff.mp hA
    exact this
  · intro x hx
    have hxF : x ∈ F := Subfield.subset_closure hx
    exact (algebraicClosure F K).algebraMap_mem ⟨x, hxF⟩

end Countable

section Coeffs

lemma eval_mem_of_coeffs {R : Type*} [CommRing R] (T : Subring R) (p : Polynomial R)
    (hp : ∀ i, p.coeff i ∈ T) {x : R} (hx : x ∈ T) : p.eval x ∈ T := by
  rw [Polynomial.eval_eq_sum_range]
  exact Subring.sum_mem _ fun i _ => mul_mem (hp i) (pow_mem hx i)

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

lemma aeval_mem_A₀ (t : Ω) (P : K[X]) (hP : ∀ i, P.coeff i ∈ (algebraMap k K).range) :
    aeval t P ∈ A₀ k t := by
  rw [aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  obtain ⟨a, ha⟩ := hP i
  rw [← ha, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  exact mul_mem (Subalgebra.algebraMap_mem _ a) (pow_mem (Algebra.self_mem_adjoin_singleton k t) i)

end Coeffs

section Up

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **`CoreStar` over an algebraically closed field from its countable algebraically closed
subfields.** -/
theorem coreStar_of_subfields (E : WeierstrassCurve K) [E.IsElliptic]
    (H : ∀ L₀ : Subfield K, IsAlgClosed L₀ → Countable L₀ → ∀ (E₀ : WeierstrassCurve L₀),
      E₀.IsElliptic → E₀.map (algebraMap L₀ K) = E → CoreStar E₀) :
    CoreStar E := by
  classical
  let Ω := AlgebraicClosure E.toAffine.FunctionField
  let j : E.toAffine.FunctionField →ₐ[K] Ω := IsScalarTower.toAlgHom K _ _
  rw [coreStar_iff_sOmega j, sOmega_iff_sOmegaTY]
  have hbm := bE_mem j
  have hcm := cE_mem j
  have hyq := yE_sq j
  generalize hT : tE j = t at hbm hcm hyq ⊢
  generalize hY : yE j = y at hyq ⊢
  intro htK hfd hsep L hLfd hLsep hL het g
  haveI : CharZero (K₀ K t) := charZero_of_injective_algebraMap (algebraMap K (K₀ K t)).injective
  -- a primitive element and the coordinates of `s`, `y`
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (K₀ K t) L
  set θ : Ω := (α : Ω)
  have hθint : IsIntegral (K₀ K t) θ :=
    (IsIntegral.of_finite (K₀ K t) α).map (IsScalarTower.toAlgHom (K₀ K t) L Ω)
  have hLθ : ∀ x ∈ L, x ∈ IntermediateField.adjoin (K₀ K t) {θ} := by
    intro x hx
    have h1 : (⟨x, hx⟩ : L) ∈ (K₀ K t)⟮α⟯ := hα ▸ IntermediateField.mem_top
    have h2 : x ∈ ((K₀ K t)⟮α⟯).map L.val := ⟨_, h1, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at h2
  have hpoly : ∀ x ∈ L, ∃ r : (K₀ K t)[X], aeval θ r = x := by
    intro x hx
    have := hLθ x hx
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at this
    exact this
  set tb := coordRingBotEquiv (Ω := Ω) htK Polynomial.X
  set s := coordRingVal t (g.f tb)
  have hsL : s ∈ L := (g.f tb).1.2
  have hyL : y ∈ L := hL (IntermediateField.subset_adjoin _ _ rfl)
  obtain ⟨rs, hrs⟩ := hpoly s hsL
  obtain ⟨ry, hry⟩ := hpoly y hyL
  set q := minpoly (K₀ K t) θ
  -- the finite set of coefficients
  let C : Finset (K₀ K t) := q.coeffs ∪ rs.coeffs ∪ ry.coeffs
  have hrep : ∀ c : K₀ K t, ∃ P Q : K[X], (c : Ω) = aeval t P / aeval t Q :=
    fun c => (IntermediateField.mem_adjoin_simple_iff _ _).mp c.2
  choose P Q hPQ using hrep
  let S : Set K := (⋃ c ∈ C, ((P c).coeffs ∪ (Q c).coeffs : Set K)) ∪
    {E.a₁, E.a₂, E.a₃, E.a₄, E.a₆}
  have hSfin : S.Finite := by
    refine Set.Finite.union (Set.Finite.biUnion C.finite_toSet fun c _ => ?_) (Set.toFinite _)
    exact Set.Finite.union (Finset.finite_toSet _) (Finset.finite_toSet _)
  obtain ⟨L₀, hL₀alg, hL₀c, hSL₀⟩ := exists_algClosed_countable S hSfin
  haveI := hL₀alg
  haveI : CharZero L₀ := ⟨fun a b h => Nat.cast_injective (R := K) (congrArg Subtype.val h)⟩
  haveI : IsScalarTower L₀ K Ω := inferInstance
  have hmemL₀ : ∀ x ∈ S, x ∈ (algebraMap L₀ K).range := fun x hx => ⟨⟨x, hSL₀ hx⟩, rfl⟩
  -- the coefficients lie in `L₀(t)`
  have hC : ∀ c ∈ C, (c : Ω) ∈ K₀ L₀ t := by
    intro c hc
    have hcoef : ∀ R : K[X], (∀ i, R.coeff i ≠ 0 → R.coeff i ∈ S) →
        aeval t R ∈ K₀ L₀ t := by
      intro R hR
      have : aeval t R ∈ A₀ L₀ t := aeval_mem_A₀ t R fun i => by
        by_cases h0 : R.coeff i = 0
        · rw [h0]; exact zero_mem _
        · exact hmemL₀ _ (hR i h0)
      exact (Algebra.adjoin_le_iff.mpr (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]; exact IntermediateField.mem_adjoin_simple_self L₀ t) :
        A₀ L₀ t ≤ (K₀ L₀ t).toSubalgebra) this
    rw [hPQ c]
    refine div_mem (hcoef _ fun i hi => ?_) (hcoef _ fun i hi => ?_)
    · refine Or.inl (Set.mem_biUnion hc (Or.inl ?_))
      exact Polynomial.coeff_mem_coeffs hi
    · refine Or.inl (Set.mem_biUnion hc (Or.inr ?_))
      exact Polynomial.coeff_mem_coeffs hi
  have hcoeff : ∀ (r : (K₀ K t)[X]), (∀ c ∈ r.coeffs, c ∈ C) →
      ∀ i, ((r.coeff i : K₀ K t) : Ω) ∈ K₀ L₀ t := by
    intro r hr i
    by_cases h0 : r.coeff i = 0
    · rw [h0]; exact zero_mem _
    · exact hC _ (hr _ (Polynomial.coeff_mem_coeffs h0))
  have hqC := hcoeff q (fun c hc => Finset.mem_union_left _ (Finset.mem_union_left _ hc))
  have hrsC := hcoeff rs (fun c hc => Finset.mem_union_left _ (Finset.mem_union_right _ hc))
  have hryC := hcoeff ry (fun c hc => Finset.mem_union_right _ hc)
  -- `θ` is integral over `L₀(t)`
  have hθ₀ : IsIntegral (K₀ L₀ t) θ := by
    set qΩ := q.map (algebraMap (K₀ K t) Ω)
    have hqc : (↑qΩ.coeffs : Set Ω) ⊆ (K₀ L₀ t).toSubring := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hz
      rw [Polynomial.coeff_map]
      exact hqC i
    let qT : (K₀ L₀ t)[X] := qΩ.toSubring (K₀ L₀ t).toSubring hqc
    refine ⟨qT, (Polynomial.monic_toSubring _ _ _).mpr ((minpoly.monic hθint).map _), ?_⟩
    have h1 : qT.map (algebraMap (K₀ L₀ t) Ω) = qΩ := Polynomial.map_toSubring qΩ _ hqc
    rw [← Polynomial.eval_map, h1, Polynomial.eval_map, ← aeval_def]
    exact minpoly.aeval _ _
  let F₀ : IntermediateField (K₀ L₀ t) Ω := IntermediateField.adjoin (K₀ L₀ t) {θ}
  haveI : FiniteDimensional (K₀ L₀ t) F₀ := IntermediateField.adjoin.finiteDimensional hθ₀
  have hθF₀ : θ ∈ F₀ := IntermediateField.mem_adjoin_simple_self _ θ
  have hmemF₀ : ∀ r : (K₀ K t)[X], (∀ i, ((r.coeff i : K₀ K t) : Ω) ∈ K₀ L₀ t) →
      aeval θ r ∈ F₀ := by
    intro r hr
    rw [aeval_def, ← Polynomial.eval_map]
    refine eval_mem_of_coeffs F₀.toSubring _ (fun i => ?_) hθF₀
    rw [Polynomial.coeff_map]
    exact F₀.algebraMap_mem ⟨_, hr i⟩
  have hsF₀ : s ∈ F₀ := hrs ▸ hmemF₀ rs hrsC
  have hyF₀ : y ∈ F₀ := hry ▸ hmemF₀ ry hryC
  have hF₀L : ∀ x ∈ F₀, x ∈ L := by
    let T : IntermediateField (K₀ L₀ t) Ω :=
      L.toSubfield.toIntermediateField fun c => L.algebraMap_mem (K₀Map t c)
    have : F₀ ≤ T := by
      rw [IntermediateField.adjoin_simple_le_iff]; exact α.2
    exact fun x hx => this hx
  have hLF₀ : L ≤ IntermediateField.adjoin (K₀ K t) (F₀ : Set Ω) := fun x hx =>
    IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr hθF₀) (hLθ x hx)
  -- the curve over `L₀`
  let E₀ : WeierstrassCurve L₀ :=
    ⟨⟨E.a₁, hSL₀ (Or.inr (by simp))⟩, ⟨E.a₂, hSL₀ (Or.inr (by simp))⟩,
      ⟨E.a₃, hSL₀ (Or.inr (by simp))⟩, ⟨E.a₄, hSL₀ (Or.inr (by simp))⟩,
      ⟨E.a₆, hSL₀ (Or.inr (by simp))⟩⟩
  have hE₀ : E₀.map (algebraMap L₀ K) = E := by
    ext <;> rfl
  haveI hE₀ell : E₀.IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr fun h0 => ?_⟩
    have := WeierstrassCurve.map_Δ E₀ (algebraMap L₀ K)
    rw [hE₀, h0, map_zero] at this
    exact (isUnit_iff_ne_zero.mp (WeierstrassCurve.IsElliptic.isUnit (W := E))) this
  have hk := H L₀ hL₀alg hL₀c E₀ hE₀ell hE₀
  obtain ⟨j₀, hj₀t, hj₀y⟩ := exists_j_of_map E₀ E hE₀ j
  rw [hT] at hj₀t
  rw [hY] at hj₀y
  have hk' := (sOmega_iff_sOmegaTY j₀).mp ((coreStar_iff_sOmega j₀).mp hk)
  have hb₀ := bE_mem j₀
  have hc₀ := cE_mem j₀
  have hy₀ := yE_sq j₀
  rw [hj₀t] at hk' hb₀ hc₀
  rw [hj₀y] at hk' hy₀
  exact eq_of_descended htK hb₀ hc₀ hy₀ hk' L hL het g F₀ hF₀L hLF₀ hyF₀ hsF₀

end Up

section Main

/-- **[CanLift], Proposition 2.7 over `ℂ`** (the non-arithmetic case): for an elliptic curve
`E / ℂ` with non-exceptional `j`-invariant, `(E ∖ {0}) / {±1}` is the `ℂ`-core of `E ∖ {0}`. -/
def CanLift27Complex : Prop :=
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], (∀ c ∈ excJ, E.j ≠ (c : ℂ)) →
    IsCoreOf (punctured E) (hemi E)

lemma j_ne_of_map {k K : Type*} [Field k] [Field K] [CharZero k] [CharZero K] (f : k →+* K)
    (E : WeierstrassCurve k) [E.IsElliptic] (hj : ∀ c ∈ excJ, E.j ≠ (c : k)) :
    ∀ c ∈ excJ, (E.map f).j ≠ (c : K) := by
  intro c hc h
  rw [WeierstrassCurve.map_j, ← map_ratCast f] at h
  exact hj c hc (f.injective h)

lemma j_ne_of_map' {k K : Type*} [Field k] [Field K] [CharZero k] [CharZero K] (f : k →+* K)
    (E : WeierstrassCurve k) [E.IsElliptic] (hj : ∀ c ∈ excJ, (E.map f).j ≠ (c : K)) :
    ∀ c ∈ excJ, E.j ≠ (c : k) := by
  intro c hc h
  apply hj c hc
  rw [WeierstrassCurve.map_j, h, map_ratCast]

/-- **The Lefschetz principle for [CanLift], Proposition 2.7**: the statement over `ℂ` implies
the statement over every field of characteristic `0`. -/
theorem canLift27_of_complex (h : CanLift27Complex) : CanLift27.{0} := by
  intro k _ _ E _ hj
  rw [isCoreOf_iff_coreStar]
  let K := AlgebraicClosure k
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  refine coreStar_of_map (algebraMap k K) E ?_
  have hjK := j_ne_of_map (algebraMap k K) E hj
  refine coreStar_of_subfields (E.map (algebraMap k K)) ?_
  intro L₀ hL₀alg hL₀c E₀ hE₀ell hE₀
  haveI : CharZero L₀ := ⟨fun a b h => Nat.cast_injective (R := K) (congrArg Subtype.val h)⟩
  obtain ⟨ι⟩ := nonempty_ringHom_complex L₀
  have hj₀ : ∀ c ∈ excJ, E₀.j ≠ (c : L₀) :=
    j_ne_of_map' (algebraMap L₀ K) E₀ (fun c hc h' => hjK c hc (by
      have e : (E₀.map (algebraMap L₀ K)).j = (E.map (algebraMap k K)).j := by
        simp only [hE₀]
      rw [← e]; exact h'))
  exact coreStar_of_map ι E₀ (coreStar_of_isCoreOf (h (E₀.map ι) (j_ne_of_map ι E₀ hj₀)))

end Main

end AffOrbicurve
