/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbicurve.EllipticSubfield
public import Pi1.Orbicurve.HemiTY

/-!
# The Lefschetz principle for [CanLift], Proposition 2.7

`AffOrbicurve.CoreStar E`: every finite étale cover of `E ∖ {0}` has at most one finite étale
morphism to `(E ∖ {0}) / {±1}`. By the criterion for cores (`isCoreOf_of_subsingleton`) this is
equivalent to `(E ∖ {0}) / {±1}` being the `k`-core of `E ∖ {0}` (`isCoreOf_iff_coreStar`), and it
is a statement about finitely many elements of finite extensions of `k(t)`, which transfers
between fields of characteristic `0`:

* `coreStar_iff_sOmega`: `CoreStar E` in terms of subfields of an algebraically closed field `Ω`
  containing `k(E)`;
* downwards along any extension `k → K` (compositum with `K(t)`; ramification indices do not
  change, `ramificationIdx_bc`);
* upwards from algebraically closed subfields over which the data are defined (lying over,
  `exists_comap_bc_eq`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial WeierstrassCurve

namespace AffOrbicurve

section CoreStar

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k)

/-- **Uniqueness of morphisms to `(E ∖ {0}) / {±1}`**: every finite étale cover of `E ∖ {0}` has
at most one finite étale morphism to `(E ∖ {0}) / {±1}`. -/
def CoreStar : Prop :=
  ∀ Z : AffOrbicurve k, Hom Z (punctured E) → Subsingleton (Hom Z (hemi E))

variable {E}

lemma coreStar_of_isCoreOf (h : IsCoreOf (punctured E) (hemi E)) : CoreStar E :=
  fun Z φ => (h.2 Z (LocBar.of_hom φ)).2

/-- The quotient map `E ∖ {0} → (E ∖ {0}) / {±1}`. -/
noncomputable def puncturedToHemi : Hom (punctured E) (hemi E) :=
  let j := IsScalarTower.toAlgHom k E.toAffine.FunctionField
    (AlgebraicClosure E.toAffine.FunctionField)
  (isoPuncturedE j).inv.comp ((homE j).comp (isoHemiE j).hom)

/-- **`(E ∖ {0}) / {±1}` is the `k`-core of `E ∖ {0}` iff morphisms to it are unique.** -/
theorem isCoreOf_iff_coreStar : IsCoreOf (punctured E) (hemi E) ↔ CoreStar E :=
  ⟨coreStar_of_isCoreOf, fun h => isCoreOf_of_subsingleton puncturedToHemi h⟩

end CoreStar

section Omega

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k}
  {Ω : Type u} [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] (j : E.toAffine.FunctionField →ₐ[k] Ω)

/-- **`CoreStar` inside `Ω`**: for every finite extension `F ⊇ k(E)` in `Ω` unramified over the
coordinate ring of `E ∖ {0}`, every finite étale morphism from the normalization of the `t`-line
in `F` to `(E ∖ {0}) / {±1}` is the canonical one. -/
def SOmega : Prop :=
  ∀ (F : IntermediateField (K₀ k (tE j)) Ω) [FiniteDimensional (K₀ k (tE j)) F]
    [Algebra.IsSeparable (K₀ k (tE j)) F] (h : fnFieldE j ≤ F),
    (∀ w : Ideal (coordRing k (tE j) F), w.IsMaximal →
      (letI := algRing (tE j) h; w.ramificationIdx (coordRing k (tE j) (fnFieldE j))) = 1) →
    ∀ g : Hom (ofSubfieldScheme (tE j) (transcendental_tE j) F) (hemiE j),
      g.f = ringMap (tE j) (bot_le : (⊥ : IntermediateField (K₀ k (tE j)) Ω) ≤ F)

set_option maxHeartbeats 1000000 in
theorem sOmega_of_coreStar (h : CoreStar E) : SOmega j := by
  intro F _ _ hF het g
  have ht := transcendental_tE j
  let Z := ofSubfieldScheme (tE j) ht F
  let φ : Hom Z (ofSubfieldScheme (tE j) ht (fnFieldE j)) :=
    homOfLE ht hF (fun w hw => by rw [mul_one]; exact het w hw)
  let c : Hom Z (hemiE j) := φ.comp (homE j)
  have hsub := h Z (φ.comp (isoPuncturedE j).hom)
  have heq := hsub.elim (g.comp (isoHemiE j).hom) (c.comp (isoHemiE j).hom)
  have h1 := congrArg (fun r : Hom Z (hemi E) => r.f.comp (isoHemiE j).inv.f) heq
  simp only [Hom.comp_f, AlgHom.comp_assoc, (isoHemiE j).hom_inv, AlgHom.comp_id] at h1
  rw [h1]
  rfl

set_option maxHeartbeats 1000000 in
theorem coreStar_of_sOmega (h : SOmega j) : CoreStar E := by
  intro Z φ
  have ht := transcendental_tE j
  haveI : CharZero (K₀ k (tE j)) :=
    charZero_of_injective_algebraMap (algebraMap k (K₀ k (tE j))).injective
  let φ' : Hom Z (ofSubfieldScheme (tE j) ht (fnFieldE j)) := φ.comp (isoPuncturedE j).inv
  obtain ⟨F, _, hF, ψ, hψ⟩ := exists_algEquiv_coordRing (tE j) Z.A φ'.f φ'.injective φ'.isIntegral
  haveI : Algebra.IsSeparable (K₀ k (tE j)) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- `Z` has trivial stabilizers
  have hm : ∀ w : Ideal Z.A, w.IsMaximal → Z.mult w = 1 := by
    intro w hw
    have := φ'.etale w hw
    exact Nat.eq_one_of_mul_eq_one_left this
  let Z' := ofSubfieldScheme (tE j) ht F
  let eZ : Iso Z' Z := Iso.ofAlgEquiv (X := Z') (Y := Z) ψ.symm (fun w hw => by
    rw [hm w hw]; rfl)
  have hf : (eZ.hom.comp φ').f = ringMap (tE j) hF := AlgHom.ext hψ
  have het : ∀ w : Ideal (coordRing k (tE j) F), w.IsMaximal →
      (letI := algRing (tE j) hF; w.ramificationIdx (coordRing k (tE j) (fnFieldE j))) = 1 := by
    intro w hw
    have := (eZ.hom.comp φ').etale w hw
    rw [hf] at this
    exact (mul_one _).symm.trans this
  refine ⟨fun a b => Hom.ext ?_⟩
  have ha := h F hF het (eZ.hom.comp (a.comp (isoHemiE j).inv))
  have hb := h F hF het (eZ.hom.comp (b.comp (isoHemiE j).inv))
  have hab := ha.trans hb.symm
  simp only [Hom.comp_f] at hab
  have h1 := congrArg (fun r => (eZ.inv.f.comp r).comp (isoHemiE j).hom.f) hab
  simp only [← AlgHom.comp_assoc, eZ.inv_hom] at h1
  simp only [AlgHom.comp_assoc, (isoHemiE j).inv_hom, AlgHom.comp_id, AlgHom.id_comp] at h1
  exact h1

theorem coreStar_iff_sOmega : CoreStar E ↔ SOmega j :=
  ⟨sOmega_of_coreStar j, coreStar_of_sOmega j⟩

end Omega

section Transfer

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω] [IsAlgClosed Ω] [CharZero k] {t : Ω} (htK : Transcendental K t)
  {F₁ F₂ : IntermediateField (K₀ k t) Ω} {F₁' F₂' : IntermediateField (K₀ K t) Ω}
  [FiniteDimensional (K₀ k t) F₂] (h : F₁ ≤ F₂) (h' : F₁' ≤ F₂')
  (h₁ : ∀ x ∈ F₁, x ∈ F₁') (h₂ : ∀ x ∈ F₂, x ∈ F₂')
  (h₁' : F₁' ≤ IntermediateField.adjoin (K₀ K t) (F₁ : Set Ω))
  (h₂' : F₂' ≤ IntermediateField.adjoin (K₀ K t) (F₂ : Set Ω))
  {m₁ : Ideal (coordRing k t F₁) → ℕ} {m₂ : Ideal (coordRing k t F₂) → ℕ}
  {m₁' : Ideal (coordRing K t F₁') → ℕ} {m₂' : Ideal (coordRing K t F₂') → ℕ}
  (hm₁ : ∀ v' : Ideal (coordRing K t F₁'), v'.IsMaximal → v'.comap (bcMap h₁) = ⊥ → m₁' v' = 1)
  (hm₁' : ∀ v' : Ideal (coordRing K t F₁'), v'.IsMaximal → v'.comap (bcMap h₁) ≠ ⊥ →
    m₁' v' = m₁ (v'.comap (bcMap h₁)))
  (hm₂ : ∀ w' : Ideal (coordRing K t F₂'), w'.IsMaximal → w'.comap (bcMap h₂) = ⊥ → m₂' w' = 1)
  (hm₂' : ∀ w' : Ideal (coordRing K t F₂'), w'.IsMaximal → w'.comap (bcMap h₂) ≠ ⊥ →
    m₂' w' = m₂ (w'.comap (bcMap h₂)))

include htK h₁' h₂' hm₁ hm₁' hm₂ hm₂' in
set_option maxHeartbeats 1000000 in
/-- **Étaleness is preserved by extension of the constant field.** -/
theorem etale_bc
    (C : ∀ w : Ideal (coordRing k t F₂), w.IsMaximal →
      (letI := algRing t h; w.ramificationIdx (coordRing k t F₁)) * m₂ w =
        m₁ (w.comap (ringMap t h))) :
    ∀ w' : Ideal (coordRing K t F₂'), w'.IsMaximal →
      (letI := algRing t h'; w'.ramificationIdx (coordRing K t F₁')) * m₂' w' =
        m₁' (w'.comap (ringMap t h')) := by
  intro w' hw'
  have htk : Transcendental k t := transcendental_of_bc (K := K) htK
  obtain ⟨hbot, hne⟩ := ramificationIdx_bc htK h h' h₁ h₂ h₁' h₂' w'
  set w := w'.comap (bcMap h₂)
  have hv : (w'.comap (ringMap t h')).comap (bcMap h₁) = w.comap (ringMap t h) := by
    ext x; exact Iff.rfl
  haveI : (w'.comap (ringMap t h')).IsMaximal := by
    letI := algRing t h'
    haveI : Algebra.IsIntegral (coordRing K t F₁') (coordRing K t F₂') :=
      ⟨ringMap_isIntegral t _⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w'
  by_cases hw : w = ⊥
  · rw [hbot hw, one_mul, hm₂ w' hw' hw, hm₁ _ inferInstance (by
      rw [hv, hw]; exact Ideal.comap_bot_of_injective _ (ringMap_injective t h))]
  · obtain ⟨hwm, he⟩ := hne hw
    have hv0 : w.comap (ringMap t h) ≠ ⊥ := by
      letI := algRing t h
      haveI : Algebra.IsIntegral (coordRing k t F₁) (coordRing k t F₂) :=
        ⟨ringMap_isIntegral t _⟩
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
      exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
    rw [he, hm₂' w' hw' hw, hm₁' _ inferInstance (by rw [hv]; exact hv0), hv]
    exact C w hwm

include htK h₁' h₂' hm₁' hm₂' in
set_option maxHeartbeats 1000000 in
/-- **Étaleness descends along an extension of algebraically closed constant fields.** -/
theorem etale_of_bc [IsAlgClosed k]
    (C : ∀ w' : Ideal (coordRing K t F₂'), w'.IsMaximal →
      (letI := algRing t h'; w'.ramificationIdx (coordRing K t F₁')) * m₂' w' =
        m₁' (w'.comap (ringMap t h'))) :
    ∀ w : Ideal (coordRing k t F₂), w.IsMaximal →
      (letI := algRing t h; w.ramificationIdx (coordRing k t F₁)) * m₂ w =
        m₁ (w.comap (ringMap t h)) := by
  intro w hw
  have htk : Transcendental k t := transcendental_of_bc (K := K) htK
  obtain ⟨w', hw', hw'w⟩ := exists_comap_bc_eq htK h₂ h₂' w
  obtain ⟨-, hne⟩ := ramificationIdx_bc htK h h' h₁ h₂ h₁' h₂' w'
  have hw0 : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (not_isField_ring t htk F₂)
  have hw'0 : w'.comap (bcMap h₂) ≠ ⊥ := by rw [hw'w]; exact hw0
  obtain ⟨-, he⟩ := hne hw'0
  have hv : (w'.comap (ringMap t h')).comap (bcMap h₁) = w.comap (ringMap t h) := by
    rw [← hw'w]; ext x; exact Iff.rfl
  haveI : (w'.comap (ringMap t h')).IsMaximal := by
    letI := algRing t h'
    haveI : Algebra.IsIntegral (coordRing K t F₁') (coordRing K t F₂') :=
      ⟨ringMap_isIntegral t _⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w'
  have hv0 : w.comap (ringMap t h) ≠ ⊥ := by
    letI := algRing t h
    haveI : Algebra.IsIntegral (coordRing k t F₁) (coordRing k t F₂) :=
      ⟨ringMap_isIntegral t _⟩
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw0
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  have := C w' hw'
  rw [he, hm₂' w' hw' hw'0, hm₁' _ inferInstance (by rw [hv]; exact hv0), hv, hw'w] at this
  exact this

end Transfer

section Rebase

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

/-- The inclusion `k[s] → k[t][s]`. -/
lemma isIntegral_A₀_trans {s t x : Ω} (hs : IsIntegral (A₀ k t) s) (hx : IsIntegral (A₀ k s) x) :
    IsIntegral (A₀ k t) x := by
  let R : Subalgebra (A₀ k t) Ω := Algebra.adjoin (A₀ k t) {s}
  haveI : Algebra.IsIntegral (A₀ k t) R :=
    Algebra.IsIntegral.adjoin (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hs)
  have hle : ∀ y ∈ A₀ k s, y ∈ R := by
    have : A₀ k s ≤ (R.restrictScalars k) := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        Subalgebra.mem_restrictScalars]
      exact Algebra.self_mem_adjoin_singleton _ s
    exact fun y hy => this hy
  let ι : A₀ k s →+* R :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hxR : IsIntegral R x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map ι, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpx
  exact isIntegral_trans x hxR

lemma transcendental_of_isIntegral {s t : Ω} (ht : Transcendental k t)
    (hts : IsIntegral (A₀ k s) t) : Transcendental k s := by
  intro hs
  apply ht
  haveI : Algebra.IsIntegral k (A₀ k s) :=
    Algebra.IsIntegral.adjoin (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hs.isIntegral)
  exact (isIntegral_trans t hts).isAlgebraic

variable {t : Ω} (F : IntermediateField (K₀ k t) Ω) {s : Ω} (hs : s ∈ F)

include hs in
lemma K₀_le_rebase : K₀ k s ≤ F.restrictScalars k := by
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
    IntermediateField.mem_restrictScalars]
  exact hs

/-- **`F` as an extension of `k(s)`**, for `s ∈ F`. -/
noncomputable def rebase : IntermediateField (K₀ k s) Ω :=
  IntermediateField.extendScalars (K₀_le_rebase F hs)

lemma mem_rebase {x : Ω} : x ∈ rebase F hs ↔ x ∈ F := Iff.rfl

variable {F hs}

lemma range_coordRingVal_rebase (hst : IsIntegral (A₀ k t) s) (hts : IsIntegral (A₀ k s) t) :
    (coordRingVal t (B := F)).range = (coordRingVal s (B := rebase F hs)).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨⟨a.1.1, (mem_rebase F hs).mpr a.1.2⟩, mem_coordRing_of_isIntegral s
      (L := rebase F hs) ((mem_rebase F hs).mpr a.1.2)
      (isIntegral_A₀_trans hts (isIntegral_of_mem_coordRing t a))⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨⟨b.1.1, (mem_rebase F hs).mp b.1.2⟩, mem_coordRing_of_isIntegral t (L := F)
      ((mem_rebase F hs).mp b.1.2) (isIntegral_A₀_trans hst (isIntegral_of_mem_coordRing s b))⟩,
      rfl⟩

/-- The isomorphism of a coordinate ring with its image in `Ω`. -/
noncomputable def coordRingRangeEquiv {u : Ω} (L : IntermediateField (K₀ k u) Ω) :
    coordRing k u L ≃+* (coordRingVal u (B := L)).range :=
  RingEquiv.ofBijective (coordRingVal u (B := L)).rangeRestrict
    ⟨fun a b h => coordRingVal_injective u (by
      have := congrArg Subtype.val h
      rwa [RingHom.coe_rangeRestrict, RingHom.coe_rangeRestrict] at this),
      (coordRingVal u (B := L)).rangeRestrict_surjective⟩

lemma coe_coordRingRangeEquiv {u : Ω} (L : IntermediateField (K₀ k u) Ω) (a : coordRing k u L) :
    ((coordRingRangeEquiv L a : (coordRingVal u (B := L)).range) : Ω) = coordRingVal u a :=
  RingHom.coe_rangeRestrict _ _

/-- The coordinate rings of `F` over the `t`-line and over the `s`-line agree when `s` is integral
over `k[t]` and `t` over `k[s]`. -/
noncomputable def rebaseEquiv (hst : IsIntegral (A₀ k t) s) (hts : IsIntegral (A₀ k s) t) :
    coordRing k t F ≃+* coordRing k s (rebase F hs) :=
  (coordRingRangeEquiv F).trans ((RingEquiv.subringCongr (range_coordRingVal_rebase hst hts)).trans
    (coordRingRangeEquiv (rebase F hs)).symm)

lemma coordRingVal_rebaseEquiv (hst : IsIntegral (A₀ k t) s) (hts : IsIntegral (A₀ k s) t)
    (a : coordRing k t F) :
    coordRingVal s (B := rebase F hs) (rebaseEquiv (hs := hs) hst hts a) = coordRingVal t a := by
  rw [← coe_coordRingRangeEquiv, ← coe_coordRingRangeEquiv]
  unfold rebaseEquiv
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact RingEquiv.coe_subringCongr_apply _ _

lemma isIntegral_K₀_trans {s' t' x : Ω} (hts : IsIntegral (K₀ k s') t')
    (hx : IsIntegral (K₀ k t') x) : IsIntegral (K₀ k s') x := by
  let R : IntermediateField (K₀ k s') Ω := IntermediateField.adjoin (K₀ k s') {t'}
  haveI : FiniteDimensional (K₀ k s') R := IntermediateField.adjoin.finiteDimensional hts
  have hle : ∀ z ∈ K₀ k t', z ∈ R := by
    let R' : IntermediateField k Ω := R.restrictScalars k
    have : K₀ k t' ≤ R' := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        IntermediateField.mem_restrictScalars]
      exact IntermediateField.mem_adjoin_simple_self _ t'
    exact fun z hz => this hz
  let ι : K₀ k t' →+* R :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hxR : IsIntegral R x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map ι, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpx
  exact isIntegral_trans x hxR

set_option maxHeartbeats 1000000 in
/-- `F` is finite over `k(s)` when `t` is integral over `k[s]`. -/
lemma finiteDimensional_rebase [CharZero k] (hts : IsIntegral (A₀ k s) t)
    [FiniteDimensional (K₀ k t) F] : FiniteDimensional (K₀ k s) (rebase F hs) := by
  haveI : CharZero (K₀ k t) := charZero_of_injective_algebraMap (algebraMap k (K₀ k t)).injective
  haveI : Algebra.IsSeparable (K₀ k t) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (K₀ k t) F
  have htK : IsIntegral (K₀ k s) t := hts.tower_top
  have hαK : IsIntegral (K₀ k s) (α : Ω) := isIntegral_K₀_trans htK
    ((IsIntegral.of_finite (K₀ k t) α).map (IsScalarTower.toAlgHom (K₀ k t) F Ω))
  let S : Set Ω := {t, (α : Ω)}
  haveI : Finite S := Set.toFinite _
  haveI : FiniteDimensional (K₀ k s) (IntermediateField.adjoin (K₀ k s) S) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro z (rfl | rfl)
      · exact htK
      · exact hαK)
  have hle : rebase F hs ≤ IntermediateField.adjoin (K₀ k s) S := by
    intro x hx
    rw [mem_rebase] at hx
    have h1 : (⟨x, hx⟩ : F) ∈ (K₀ k t)⟮α⟯ := hα ▸ IntermediateField.mem_top
    have h2 : x ∈ ((K₀ k t)⟮α⟯).map F.val := ⟨_, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    let T : IntermediateField (K₀ k t) Ω :=
      (IntermediateField.adjoin (K₀ k s) S).toSubfield.toIntermediateField (fun c => by
        have : K₀ k t ≤ (IntermediateField.adjoin (K₀ k s) S).restrictScalars k := by
          rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
            IntermediateField.mem_restrictScalars]
          exact IntermediateField.subset_adjoin _ _ (Or.inl rfl)
        exact this c.2)
    have h3 : (K₀ k t)⟮(F.val α)⟯ ≤ T := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin (K₀ k s) S (Or.inr rfl)
    exact h3 h2
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

end Rebase

section SOmegaTY

variable (F : Type u) {Ω : Type u} [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (t y : Ω)

/-- **`CoreStar` for a double cover `F(t)(y)` of the `t`-line**, in terms of the elements
`t, y ∈ Ω`: every finite étale morphism to the quotient orbicurve `hemiTY F t y` from the
normalization of the `t`-line in a finite extension of `F(t)(y)` unramified over the coordinate
ring of `F(t)(y)` is the canonical one. -/
def SOmegaTY : Prop :=
  ∀ (ht : Transcendental F t) [FiniteDimensional (K₀ F t) (fnTY F t y)]
    [Algebra.IsSeparable (K₀ F t) (fnTY F t y)]
    (L : IntermediateField (K₀ F t) Ω) [FiniteDimensional (K₀ F t) L]
    [Algebra.IsSeparable (K₀ F t) L] (h : fnTY F t y ≤ L),
    (∀ w : Ideal (coordRing F t L), w.IsMaximal →
      (letI := algRing t h; w.ramificationIdx (coordRing F t (fnTY F t y))) = 1) →
    ∀ g : Hom (ofSubfieldScheme t ht L) (hemiTY F t y ht),
      g.f = ringMap t (bot_le : (⊥ : IntermediateField (K₀ F t) Ω) ≤ L)

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]
  [Algebra k Ω] [IsAlgClosed Ω] (j : E.toAffine.FunctionField →ₐ[k] Ω)

instance finiteDimensional_fnTY_tE : FiniteDimensional (K₀ k (tE j)) (fnTY k (tE j) (yE j)) :=
  finiteDimensional_fnFieldE j

instance isSeparable_fnTY_tE : Algebra.IsSeparable (K₀ k (tE j)) (fnTY k (tE j) (yE j)) :=
  isSeparable_fnFieldE j

instance normal_fnTY_tE : Normal (K₀ k (tE j)) (fnTY k (tE j) (yE j)) :=
  normal_fnFieldE j

example : hemiE j = hemiTY k (tE j) (yE j) (transcendental_tE j) := rfl

omit [E.IsElliptic] [IsAlgClosed Ω] in
theorem sOmega_iff_sOmegaTY : SOmega j ↔ SOmegaTY k (tE j) (yE j) := by
  constructor
  · intro h ht _ _ L _ _ hL het g
    exact h L hL het g
  · intro h L _ _ hL het g
    exact h (transcendental_tE j) L hL het g

end SOmegaTY

section SMap

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] {t s : Ω}
  (ht : Transcendental F t) (hs : Transcendental F s)

/-- `F[t] ≅ F[s]`, `t ↦ s`. -/
noncomputable def lineEquiv :
    coordRing F t (⊥ : IntermediateField (K₀ F t) Ω) ≃ₐ[F]
      coordRing F s (⊥ : IntermediateField (K₀ F s) Ω) :=
  (coordRingBotEquiv ht).symm.trans (coordRingBotEquiv hs)

lemma lineEquiv_apply (p : F[X]) :
    lineEquiv ht hs (coordRingBotEquiv ht p) = coordRingBotEquiv hs p := by
  simp [lineEquiv]

variable {L : IntermediateField (K₀ F t) Ω} (hsL : s ∈ L) (hst : IsIntegral (A₀ F t) s)
  (hts : IsIntegral (A₀ F s) t)

/-- **The map of coordinate rings `F[t] → coordRing L`, `t ↦ s`.** -/
noncomputable def sHomRing :
    coordRing F t (⊥ : IntermediateField (K₀ F t) Ω) →+* coordRing F t L :=
  (rebaseEquiv (hs := hsL) hst hts).symm.toRingHom.comp
    ((ringMap s (bot_le : (⊥ : IntermediateField (K₀ F s) Ω) ≤ rebase L hsL)).toRingHom.comp
      (lineEquiv ht hs).toRingEquiv.toRingHom)

lemma coordRingVal_sHomRing (a : coordRing F t (⊥ : IntermediateField (K₀ F t) Ω)) :
    coordRingVal t (sHomRing ht hs hsL hst hts a) = coordRingVal s (lineEquiv ht hs a) := by
  rw [← coordRingVal_rebaseEquiv (hs := hsL) hst hts, sHomRing, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rfl

lemma coordRingVal_sHomRing_poly (p : F[X]) :
    coordRingVal t (sHomRing ht hs hsL hst hts (coordRingBotEquiv ht p)) = aeval s p := by
  rw [coordRingVal_sHomRing, lineEquiv_apply]
  exact coe_coordRingBotEquiv hs p

/-- **The map of coordinate rings `F[t] → coordRing L`, `t ↦ s`**, as an `F`-algebra map. -/
noncomputable def sHom :
    coordRing F t (⊥ : IntermediateField (K₀ F t) Ω) →ₐ[F] coordRing F t L :=
  { sHomRing ht hs hsL hst hts with
    commutes' := fun c => by
      apply coordRingVal_injective t
      change coordRingVal t (sHomRing ht hs hsL hst hts (algebraMap F _ c)) = _
      have : algebraMap F (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω)) c =
          coordRingBotEquiv ht (Polynomial.C c) := by
        rw [← Polynomial.algebraMap_eq, AlgEquiv.commutes]
      rw [this, coordRingVal_sHomRing_poly, aeval_C]
      rfl }

lemma sHom_apply (a) : sHom ht hs hsL hst hts a = sHomRing ht hs hsL hst hts a := rfl

lemma sHom_injective : Function.Injective (sHom ht hs hsL hst hts) := by
  intro a b hab
  have h := congrArg (coordRingVal t) hab
  rw [sHom_apply, sHom_apply, coordRingVal_sHomRing, coordRingVal_sHomRing] at h
  exact (lineEquiv ht hs).injective (coordRingVal_injective s h)

lemma sHom_isIntegral : (sHom ht hs hsL hst hts).toRingHom.IsIntegral := by
  change (sHomRing ht hs hsL hst hts).IsIntegral
  unfold sHomRing
  refine RingHom.IsIntegral.trans _ _ (RingHom.IsIntegral.trans _ _ ?_ ?_) ?_
  · exact RingHom.IsIntegral.of_finite (RingHom.Finite.of_surjective _ (lineEquiv ht hs).surjective)
  · exact ringMap_isIntegral s _
  · exact RingHom.IsIntegral.of_finite
      (RingHom.Finite.of_surjective _ (rebaseEquiv (hs := hsL) hst hts).symm.surjective)

include ht in
lemma algHom_bot_ext {B : Type*} [CommRing B] [Algebra F B]
    {f g : coordRing F t (⊥ : IntermediateField (K₀ F t) Ω) →ₐ[F] B}
    (h : f (coordRingBotEquiv ht Polynomial.X) = g (coordRingBotEquiv ht Polynomial.X)) :
    f = g := by
  have : f.comp (coordRingBotEquiv ht).toAlgHom = g.comp (coordRingBotEquiv ht).toAlgHom :=
    Polynomial.algHom_ext h
  ext a
  obtain ⟨p, rfl⟩ := (coordRingBotEquiv ht).surjective a
  exact congrArg (fun φ : F[X] →ₐ[F] B => φ p) this

variable [CharZero F] [FiniteDimensional (K₀ F t) L]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Étaleness of `t ↦ s` in terms of the `s`-line**. -/
lemma etale_sHom_iff (m : Ideal (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω)) → ℕ) :
    (∀ w : Ideal (coordRing F t L), w.IsMaximal →
      (letI := (sHom ht hs hsL hst hts).toRingHom.toAlgebra;
        w.ramificationIdx (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω))) * 1 =
        m (w.comap (sHom ht hs hsL hst hts))) ↔
    (∀ ws : Ideal (coordRing F s (rebase L hsL)), ws.IsMaximal →
      (letI := algRing s (bot_le : (⊥ : IntermediateField (K₀ F s) Ω) ≤ rebase L hsL);
        ws.ramificationIdx (coordRing F s (⊥ : IntermediateField (K₀ F s) Ω))) * 1 =
        m ((ws.comap (ringMap s (bot_le : (⊥ : IntermediateField (K₀ F s) Ω) ≤ rebase L hsL))).comap
          (lineEquiv ht hs).toRingEquiv.toRingHom)) := by
  haveI : FiniteDimensional (K₀ F s) (rebase L hsL) := finiteDimensional_rebase (hs := hsL) hts
  haveI : CharZero (K₀ F s) := charZero_of_injective_algebraMap (algebraMap F (K₀ F s)).injective
  haveI : Algebra.IsSeparable (K₀ F s) (rebase L hsL) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : CharZero (K₀ F t) := charZero_of_injective_algebraMap (algebraMap F (K₀ F t)).injective
  haveI : Algebra.IsSeparable (K₀ F t) L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI := isDedekindDomain_ring t ht L
  haveI := isDedekindDomain_ring t ht (⊥ : IntermediateField (K₀ F t) Ω)
  haveI := isDedekindDomain_ring s hs (rebase L hsL)
  haveI := isDedekindDomain_ring s hs (⊥ : IntermediateField (K₀ F s) Ω)
  set β := rebaseEquiv (hs := hsL) hst hts
  have hcompat : ∀ r, β ((sHom ht hs hsL hst hts).toRingHom r) =
      (ringMap s (bot_le : (⊥ : IntermediateField (K₀ F s) Ω) ≤ rebase L hsL)).toRingHom
        ((lineEquiv ht hs).toRingEquiv r) := by
    intro r
    change β (β.symm _) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  have he : ∀ w : Ideal (coordRing F t L), w.IsPrime →
      (letI := (sHom ht hs hsL hst hts).toRingHom.toAlgebra;
        w.ramificationIdx (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω))) =
      (letI := algRing s (bot_le : (⊥ : IntermediateField (K₀ F s) Ω) ≤ rebase L hsL);
        (w.comap β.symm.toRingHom).ramificationIdx
          (coordRing F s (⊥ : IntermediateField (K₀ F s) Ω))) := by
    intro w hw
    exact ramificationIdx_congr (sHom ht hs hsL hst hts).toRingHom
      (ringMap s (bot_le : (⊥ : IntermediateField (K₀ F s) Ω) ≤ rebase L hsL)).toRingHom
      (lineEquiv ht hs).toRingEquiv β hcompat (ringMap_injective s _) w
  have hc : ∀ w : Ideal (coordRing F t L),
      ((w.comap β.symm.toRingHom).comap
        (ringMap s (bot_le : (⊥ : IntermediateField (K₀ F s) Ω) ≤ rebase L hsL))).comap
          (lineEquiv ht hs).toRingEquiv.toRingHom = w.comap (sHom ht hs hsL hst hts) := by
    intro w; ext x; exact Iff.rfl
  constructor
  · intro H ws hws
    set w := ws.comap β.toRingHom
    haveI : w.IsMaximal := Ideal.comap_isMaximal_of_surjective _ β.surjective
    have hws' : ws = w.comap β.symm.toRingHom := (comap_comap_symm β.symm ws).symm
    have := H w inferInstance
    rw [he w inferInstance] at this
    rw [hws', hc]
    exact this
  · intro H w hw
    have := H (w.comap β.symm.toRingHom)
      (Ideal.comap_isMaximal_of_surjective _ β.symm.surjective)
    rw [hc] at this
    rw [he w hw.isPrime]
    exact this

end SMap

section BCAux

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

omit [Algebra k K] [Algebra k Ω] [IsScalarTower k K Ω] in
/-- Changing the parameter of a compositum. -/
lemma adjoin_param_le {u v : Ω} {S : Set Ω}
    (hu : u ∈ IntermediateField.adjoin (K₀ K v) S) {x : Ω}
    (hx : x ∈ IntermediateField.adjoin (K₀ K u) S) : x ∈ IntermediateField.adjoin (K₀ K v) S := by
  rw [← IntermediateField.mem_restrictScalars K, IntermediateField.restrictScalars_adjoin] at hx ⊢
  refine (IntermediateField.adjoin_le_iff.mpr ?_) hx
  rintro z (hz | hz)
  · have : K₀ K u ≤ IntermediateField.adjoin K ((K₀ K v : Set Ω) ∪ S) := by
      rw [IntermediateField.adjoin_simple_le_iff, ← IntermediateField.restrictScalars_adjoin,
        IntermediateField.mem_restrictScalars]
      exact hu
    exact this hz
  · exact IntermediateField.subset_adjoin _ _ (Or.inr hz)

variable [IsAlgClosed Ω] [CharZero k] {t : Ω}

lemma finiteDimensional_bc (L : IntermediateField (K₀ k t) Ω)
    [FiniteDimensional (K₀ k t) L] :
    FiniteDimensional (K₀ K t) (IntermediateField.adjoin (K₀ K t) (L : Set Ω)) := by
  obtain ⟨N, N', hLN, _, _, _, _, hNN', hN'⟩ := exists_galois_bc (K := K) L
  have hle : IntermediateField.adjoin (K₀ K t) (L : Set Ω) ≤ N' := by
    rw [hN']
    exact IntermediateField.adjoin.mono _ _ _ hLN
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

omit [IsAlgClosed Ω] [CharZero k] in
lemma lineEquiv_bcMap {s : Ω} (htk : Transcendental k t) (hsk : Transcendental k s)
    (htK : Transcendental K t) (hsK : Transcendental K s)
    (a : coordRing k t (⊥ : IntermediateField (K₀ k t) Ω)) :
    lineEquiv htK hsK (bcMap (bot_mem_bc (k := k) (K := K) (t := t)) a) =
      bcMap (bot_mem_bc (k := k) (K := K) (t := s)) (lineEquiv htk hsk a) := by
  obtain ⟨q, rfl⟩ := (coordRingBotEquiv htk).surjective a
  rw [bcMap_coordRingBotEquiv htk htK, lineEquiv_apply, lineEquiv_apply,
    bcMap_coordRingBotEquiv hsk hsK]

end BCAux

section HomAux

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] {t : Ω} (ht : Transcendental F t)
  {L : IntermediateField (K₀ F t) Ω}
  (f : coordRing F t (⊥ : IntermediateField (K₀ F t) Ω) →ₐ[F] coordRing F t L)

lemma coordRingVal_aeval (a : coordRing F t L) (p : F[X]) :
    coordRingVal t (aeval a p) = aeval (coordRingVal t a) p := by
  induction p using Polynomial.induction_on with
  | C c =>
    rw [aeval_C, aeval_C]
    rfl
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval a), map_mul, map_mul (aeval (coordRingVal t a)),
      ih, aeval_X, aeval_X]

lemma coordRingVal_algHom_bot (p : F[X]) :
    coordRingVal t (f (coordRingBotEquiv ht p)) =
      aeval (coordRingVal t (f (coordRingBotEquiv ht Polynomial.X))) p := by
  have h1 : (f.comp (coordRingBotEquiv ht).toAlgHom) =
      aeval ((f.comp (coordRingBotEquiv ht).toAlgHom) Polynomial.X) :=
    Polynomial.algHom_ext (by rw [aeval_X])
  have h2 := congrArg (fun φ : F[X] →ₐ[F] coordRing F t L => φ p) h1
  change f (coordRingBotEquiv ht p) = aeval (f (coordRingBotEquiv ht Polynomial.X)) p at h2
  rw [h2, coordRingVal_aeval]

include ht in
/-- If `t ↦ s` makes the coordinate ring of `L` integral over `F[t]`, then `t` is integral over
`F[s]`. -/
lemma isIntegral_of_algHom (hf : f.toRingHom.IsIntegral) :
    IsIntegral (A₀ F (coordRingVal t (f (coordRingBotEquiv ht Polynomial.X)))) t := by
  set s := coordRingVal t (f (coordRingBotEquiv ht Polynomial.X))
  let φ : coordRing F t (⊥ : IntermediateField (K₀ F t) Ω) →+* A₀ F s :=
    ((coordRingVal t).comp f.toRingHom).codRestrict (A₀ F s).toSubring (fun a => by
      obtain ⟨p, rfl⟩ := (coordRingBotEquiv ht).surjective a
      change coordRingVal t (f (coordRingBotEquiv ht p)) ∈ A₀ F s
      rw [coordRingVal_algHom_bot]
      exact Polynomial.aeval_mem_adjoin_singleton F s)
  let tL : coordRing F t L := ringMap t (bot_le : (⊥ : IntermediateField (K₀ F t) Ω) ≤ L)
    (coordRingBotEquiv ht Polynomial.X)
  obtain ⟨p, hp, hpt⟩ := hf tL
  refine ⟨p.map φ, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have htL : coordRingVal t tL = t := coe_coordRingBotEquiv ht Polynomial.X |>.trans (by simp)
  have := Polynomial.hom_eval₂ p f.toRingHom (coordRingVal t) tL
  rw [hpt, map_zero, htL] at this
  exact this.symm

end HomAux

section Down

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω] [IsAlgClosed Ω] [CharZero k] {t y : Ω}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **`SOmegaTY` descends along any extension of the constant field.** -/
theorem sOmegaTY_down [CharZero K] (htK : Transcendental K t) {b c : Ω} (hb : b ∈ K₀ k t)
    (hc : c ∈ K₀ k t)
    (hy : y ^ 2 + b * y = c) (hK : SOmegaTY K t y) : SOmegaTY k t y := by
  intro ht _ _ L _ _ hL het g
  haveI : Normal (K₀ k t) (fnTY k t y) := normal_fnTY hb hc hy
  haveI : FiniteDimensional (K₀ K t) (fnTY K t y) :=
    finiteDimensional_fnTY (K₀_le_bc t hb) (K₀_le_bc t hc) hy
  haveI : Algebra.IsSeparable (K₀ K t) (fnTY K t y) := isSeparable_fnTY
  haveI : Normal (K₀ K t) (fnTY K t y) := normal_fnTY (K₀_le_bc t hb) (K₀_le_bc t hc) hy
  -- the base change `L'` of `L`
  set L' := IntermediateField.adjoin (K₀ K t) (L : Set Ω)
  have hLL' : ∀ x ∈ L, x ∈ L' := fun x hx => IntermediateField.subset_adjoin _ _ hx
  haveI : FiniteDimensional (K₀ K t) L' := finiteDimensional_bc (K := K) L
  haveI : CharZero (K₀ K t) := charZero_of_injective_algebraMap (algebraMap K (K₀ K t)).injective
  haveI : Algebra.IsSeparable (K₀ K t) L' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hyL : y ∈ L := hL (IntermediateField.subset_adjoin _ _ rfl)
  have hL' : fnTY K t y ≤ L' := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact hLL' y hyL
  have h₁' : fnTY K t y ≤ IntermediateField.adjoin (K₀ K t) (fnTY k t y : Set Ω) := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin _ _ (IntermediateField.subset_adjoin _ _ rfl)
  have het' := etale_bc htK hL hL' (fnTY_mem_bc y) hLL' h₁' le_rfl
    (m₁ := fun _ => 1) (m₂ := fun _ => 1) (m₁' := fun _ => 1) (m₂' := fun _ => 1)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun w hw => by rw [mul_one]; exact het w hw)
  have het'' : ∀ w : Ideal (coordRing K t L'), w.IsMaximal →
      (letI := algRing t hL'; w.ramificationIdx (coordRing K t (fnTY K t y))) = 1 :=
    fun w hw => (mul_one _).symm.trans (het' w hw)
  -- the element `s`
  set tb := coordRingBotEquiv (Ω := Ω) ht Polynomial.X
  set s := coordRingVal t (g.f tb)
  have hsL : s ∈ L := (g.f tb).1.2
  have hst : IsIntegral (A₀ k t) s := isIntegral_of_mem_coordRing t (g.f tb)
  have hts : IsIntegral (A₀ k s) t := isIntegral_of_algHom ht g.f g.isIntegral
  have hs : Transcendental k s := transcendental_of_isIntegral ht hts
  have hg : g.f = sHom ht hs hsL hst hts := by
    apply algHom_bot_ext ht
    apply coordRingVal_injective t
    change s = coordRingVal t (sHomRing ht hs hsL hst hts tb)
    rw [coordRingVal_sHomRing_poly, aeval_X]
  -- the étale condition on the `s`-line over `k`
  have Hk := (etale_sHom_iff ht hs hsL hst hts (multTY k t y)).mp (fun w hw => by
    have := g.etale w hw
    rw [hg] at this
    exact this)
  -- over `K`
  have hsK : Transcendental K s := transcendental_of_isIntegral htK (isIntegral_A₀_of s hts)
  have hstK : IsIntegral (A₀ K t) s := isIntegral_A₀_of t hst
  have htsK : IsIntegral (A₀ K s) t := isIntegral_A₀_of s hts
  have hsL' : s ∈ L' := hLL' s hsL
  haveI : FiniteDimensional (K₀ k s) (rebase L hsL) := finiteDimensional_rebase (hs := hsL) hts
  have h₂s : ∀ x ∈ rebase L hsL, x ∈ rebase L' hsL' := fun x hx => hLL' x hx
  have h₂s' : rebase L' hsL' ≤ IntermediateField.adjoin (K₀ K s) (rebase L hsL : Set Ω) :=
    fun x hx => adjoin_param_le (IntermediateField.subset_adjoin _ _
      (L.algebraMap_mem ⟨t, IntermediateField.mem_adjoin_simple_self k t⟩)) hx
  have hle_s : (⊥ : IntermediateField (K₀ k s) Ω) ≤ rebase L hsL := bot_le
  have hle_s' : (⊥ : IntermediateField (K₀ K s) Ω) ≤ rebase L' hsL' := bot_le
  have h₁s' : (⊥ : IntermediateField (K₀ K s) Ω) ≤
      IntermediateField.adjoin (K₀ K s) ((⊥ : IntermediateField (K₀ k s) Ω) : Set Ω) := bot_le
  have hcomm : ∀ v' : Ideal (coordRing K s (⊥ : IntermediateField (K₀ K s) Ω)),
      (v'.comap (lineEquiv htK hsK).toRingEquiv.toRingHom).comap
        (bcMap (bot_mem_bc (k := k) (K := K) (t := t))) =
      (v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := s)))).comap
        (lineEquiv ht hs).toRingEquiv.toRingHom := by
    intro v'
    ext x
    simp only [Ideal.mem_comap]
    change lineEquiv htK hsK (bcMap (bot_mem_bc (k := k) (K := K) (t := t)) x) ∈ v' ↔
      bcMap (bot_mem_bc (k := k) (K := K) (t := s)) (lineEquiv ht hs x) ∈ v'
    rw [lineEquiv_bcMap ht hs htK hsK]
  have HK := etale_bc (t := s) hsK hle_s hle_s' bot_mem_bc h₂s h₁s' h₂s'
    (m₁ := fun v => multTY k t y (v.comap (lineEquiv ht hs).toRingEquiv.toRingHom))
    (m₂ := fun _ => 1)
    (m₁' := fun v' => multTY K t y (v'.comap (lineEquiv htK hsK).toRingEquiv.toRingHom))
    (m₂' := fun _ => 1)
    (fun v' hv' h0 => by
      haveI : (v'.comap (lineEquiv htK hsK).toRingEquiv.toRingHom).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ (lineEquiv htK hsK).surjective
      refine (multTY_bc (k := k) y htK _).1 ?_
      rw [hcomm, h0]
      exact Ideal.comap_bot_of_injective _ (lineEquiv ht hs).injective)
    (fun v' hv' h0 => by
      haveI : (v'.comap (lineEquiv htK hsK).toRingEquiv.toRingHom).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ (lineEquiv htK hsK).surjective
      have hne : (v'.comap (lineEquiv htK hsK).toRingEquiv.toRingHom).comap
          (bcMap (bot_mem_bc (k := k) (K := K) (t := t))) ≠ ⊥ := by
        rw [hcomm]
        intro h0'
        apply h0
        have e := comap_comap_symm (lineEquiv ht hs).toRingEquiv.symm
          (v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := s))))
        rw [RingEquiv.symm_symm] at e
        rw [← e, h0']
        exact Ideal.comap_bot_of_injective _ (lineEquiv ht hs).toRingEquiv.symm.injective
      change multTY K t y _ = multTY k t y _
      rw [(multTY_bc (k := k) y htK _).2 hne, hcomm])
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun w hw => Hk w hw)
  -- the morphism over `K`
  have hetK := (etale_sHom_iff htK hsK hsL' hstK htsK (multTY K t y)).mpr (fun w hw => HK w hw)
  let g' : Hom (ofSubfieldScheme t htK L') (hemiTY K t y htK) :=
    { f := sHom htK hsK hsL' hstK htsK
      injective := sHom_injective htK hsK hsL' hstK htsK
      isIntegral := sHom_isIntegral htK hsK hsL' hstK htsK
      etale := hetK }
  have hg' := hK htK L' hL' het'' g'
  have hst' : s = t := by
    have := congrArg (fun φ => coordRingVal t (φ (coordRingBotEquiv (Ω := Ω) htK Polynomial.X))) hg'
    change coordRingVal t (sHomRing htK hsK hsL' hstK htsK _) = _ at this
    rw [coordRingVal_sHomRing_poly, aeval_X] at this
    rw [this]
    exact (coe_coordRingBotEquiv htK Polynomial.X).trans (aeval_X t)
  apply algHom_bot_ext ht
  apply coordRingVal_injective t
  change s = _
  rw [hst']
  exact ((coe_coordRingBotEquiv ht Polynomial.X).trans (aeval_X t)).symm

end Down

section MapFF

variable {k K : Type u} [Field k] [Field K] (f : k →+* K) (E : WeierstrassCurve k)

/-- The map of function fields `k(E) → K(E_K)`. -/
noncomputable def ffMap : E.toAffine.FunctionField →+* (E.map f).toAffine.FunctionField :=
  IsFractionRing.lift (A := E.toAffine.CoordinateRing)
    (g := (algebraMap (E.map f).toAffine.CoordinateRing (E.map f).toAffine.FunctionField).comp
      (Affine.CoordinateRing.map E.toAffine f))
    ((IsFractionRing.injective _ _).comp (Affine.CoordinateRing.map_injective f.injective))

lemma ffMap_algebraMap (a : E.toAffine.CoordinateRing) :
    ffMap f E (algebraMap _ _ a) = algebraMap _ _ (Affine.CoordinateRing.map E.toAffine f a) :=
  IsFractionRing.lift_algebraMap _ _

lemma ffMap_ellX : ffMap f E (ellX E) = ellX (E.map f) := by
  rw [ellX, ffMap_algebraMap, Affine.CoordinateRing.map_mk]
  simp [ellX]

lemma ffMap_ellY : ffMap f E (ellY E) = ellY (E.map f) := by
  rw [ellY, ffMap_algebraMap, Affine.CoordinateRing.map_mk]
  simp [ellY]

end MapFF

section Weq

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {E : WeierstrassCurve k}
  (j : E.toAffine.FunctionField →ₐ[k] Ω)

/-- `b = a₁ t + a₃`. -/
noncomputable def bE : Ω := algebraMap k Ω E.a₁ * tE j + algebraMap k Ω E.a₃

/-- `c = t³ + a₂ t² + a₄ t + a₆`. -/
noncomputable def cE : Ω := tE j ^ 3 + algebraMap k Ω E.a₂ * tE j ^ 2 +
  algebraMap k Ω E.a₄ * tE j + algebraMap k Ω E.a₆

lemma bE_mem : bE j ∈ K₀ k (tE j) :=
  add_mem (mul_mem ((K₀ k (tE j)).algebraMap_mem _) (tE_mem_K₀ j)) ((K₀ k (tE j)).algebraMap_mem _)

lemma cE_mem : cE j ∈ K₀ k (tE j) := by
  have ht := tE_mem_K₀ j
  unfold cE
  refine add_mem (add_mem (add_mem (pow_mem ht 3) (mul_mem ((K₀ k (tE j)).algebraMap_mem _)
    (pow_mem ht 2))) (mul_mem ((K₀ k (tE j)).algebraMap_mem _) ht))
    ((K₀ k (tE j)).algebraMap_mem _)

lemma yE_sq : yE j ^ 2 + bE j * yE j = cE j := by
  have h' := congrArg j (ellY_sq E)
  simp only [map_add, map_mul, map_pow, AlgHom.commutes] at h'
  exact h'

end Weq

section CoreStarMap

variable {k K : Type u} [Field k] [Field K] [CharZero k] (f : k →+* K)
  (E : WeierstrassCurve k)

set_option maxHeartbeats 1000000 in
/-- **`CoreStar` descends along any field embedding.** -/
theorem coreStar_of_map [CharZero K] [(E.map f).IsElliptic] (h : CoreStar (E.map f)) :
    CoreStar E := by
  letI : Algebra k K := f.toAlgebra
  let E' := E.map f
  let Ω := AlgebraicClosure E'.toAffine.FunctionField
  haveI : IsScalarTower k K Ω := inferInstance
  let jK : E'.toAffine.FunctionField →ₐ[K] Ω := IsScalarTower.toAlgHom K _ _
  let jk : E.toAffine.FunctionField →ₐ[k] Ω :=
    { (jK.toRingHom.comp (ffMap f E)) with
      commutes' := fun c => by
        change jK (ffMap f E (algebraMap k _ c)) = algebraMap k Ω c
        rw [IsScalarTower.algebraMap_apply k K Ω]
        change _ = algebraMap K Ω (f c)
        have : algebraMap k E.toAffine.FunctionField c =
            algebraMap E.toAffine.CoordinateRing _ (algebraMap k _ c) := rfl
        rw [this, ffMap_algebraMap]
        have h2 : Affine.CoordinateRing.map E.toAffine f (algebraMap k _ c) =
            algebraMap K E'.toAffine.CoordinateRing (f c) := by
          change Affine.CoordinateRing.map E.toAffine f (Affine.CoordinateRing.mk _ (C (C c))) = _
          rw [Affine.CoordinateRing.map_mk]
          simp; rfl
        rw [h2, ← IsScalarTower.algebraMap_apply, AlgHom.commutes] }
  have ht : tE jk = tE jK := by
    change jK (ffMap f E (ellX E)) = _
    rw [ffMap_ellX]; rfl
  have hy : yE jk = yE jK := by
    change jK (ffMap f E (ellY E)) = _
    rw [ffMap_ellY]; rfl
  rw [coreStar_iff_sOmega jk, sOmega_iff_sOmegaTY]
  rw [coreStar_iff_sOmega jK, sOmega_iff_sOmegaTY] at h
  have hb : bE jk ∈ K₀ k (tE jK) := ht ▸ bE_mem jk
  have hc : cE jk ∈ K₀ k (tE jK) := ht ▸ cE_mem jk
  have heq : yE jK ^ 2 + bE jk * yE jK = cE jk := hy ▸ yE_sq jk
  rw [ht, hy]
  exact sOmegaTY_down (transcendental_tE jK) hb hc heq h

end CoreStarMap

end AffOrbicurve
