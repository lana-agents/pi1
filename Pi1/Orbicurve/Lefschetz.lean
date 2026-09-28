module

public import Pi1.Orbicurve.EllipticSubfield

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

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

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

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]
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

end Rebase

end AffOrbicurve
