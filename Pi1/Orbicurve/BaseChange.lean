module

public import Pi1.Orbicurve.CoreCriterion
public import Pi1.Orbicurve.ValuationInertia

/-!
# Ramification of subfield orbicurves under extension of the constant field

Let `k ⊆ K` be fields of characteristic `0`, `Ω ⊇ K` a field and `t ∈ Ω` transcendental over `K`.
A finite extension `F` of `k(t)` inside `Ω` has the **base change** `F_K = K(t) · F` (the
compositum inside `Ω`, `IntermediateField.adjoin (K₀ K t) F`), a finite extension of `K(t)`, and
the coordinate ring of `F` maps to that of `F_K` (`AffOrbicurve.bcMap`).

* `AffOrbicurve.res`: for a finite Galois `N / k(t)` with base change `N_K`, restriction
  `Gal(N_K / K(t)) → Gal(N / k(t))` (injective).
* `AffOrbicurve.ramificationIdx_bc`: **ramification indices are invariant under base change**:
  for `F₁ ⊆ F₂` and a maximal ideal `w'` of the coordinate ring of `F₂,K`, the prime
  `w = w' ∩ coordRing F₂` is either `0`, and then `w'` is unramified over `F₁,K`, or maximal, and
  then `e(w' | w' ∩ F₁,K) = e(w | w ∩ F₁)`. The proof compares inertia groups: restriction maps the
  inertia group `I_{u'}` of a prime of `N_K` injectively into the inertia group of `u' ∩ N`, and
  `|I_{u'}| = e(u' | K[t]) ≥ e(u | k[t]) = |I_u|` since `k[t] → K[t]` is unramified (a separable
  irreducible polynomial stays squarefree).
* `AffOrbicurve.exists_comap_bc_eq`: if `k` is algebraically closed, every maximal ideal of the
  coordinate ring of `F` lies under one of `F_K` (restriction is then an isomorphism of Galois
  groups, since `K(t) ∩ N = k(t)`: `AffOrbicurve.mem_K₀_of_isAlgebraic`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω] (t : Ω)

section Basic

lemma K₀_le_bc {x : Ω} (hx : x ∈ K₀ k t) : x ∈ K₀ K t := by
  have h : (K₀ k t) ≤ (K₀ K t).restrictScalars k := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      IntermediateField.mem_restrictScalars]
    exact IntermediateField.mem_adjoin_simple_self K t
  exact h hx

lemma A₀_le_bc {x : Ω} (hx : x ∈ A₀ k t) : x ∈ A₀ K t := by
  have h : A₀ k t ≤ (A₀ K t).restrictScalars k := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Subalgebra.mem_restrictScalars]
    exact Algebra.self_mem_adjoin_singleton K t
  exact h hx

/-- The inclusion `k[t] → K[t]`. -/
noncomputable def A₀Map : A₀ k t →+* A₀ K t where
  toFun a := ⟨a, A₀_le_bc t a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/-- The inclusion `k(t) → K(t)`. -/
noncomputable def K₀Map : K₀ k t →+* K₀ K t where
  toFun a := ⟨a, K₀_le_bc t a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

lemma isIntegral_A₀_of {x : Ω} (hx : IsIntegral (A₀ k t) x) : IsIntegral (A₀ K t) x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (A₀Map t), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpx

lemma isIntegral_K₀_of {x : Ω} (hx : IsIntegral (K₀ k t) x) : IsIntegral (K₀ K t) x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (K₀Map t), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpx

variable {t}

/-- **The ring map of coordinate rings** `coordRing F → coordRing F'` for `F ⊆ F'`, `F` over `k(t)`,
`F'` over `K(t)`. -/
noncomputable def bcMap {F : IntermediateField (K₀ k t) Ω} {F' : IntermediateField (K₀ K t) Ω}
    (h : ∀ x ∈ F, x ∈ F') : coordRing k t F →+* coordRing K t F' where
  toFun a := ⟨⟨a.1.1, h _ a.1.2⟩, mem_coordRing_of_isIntegral (k := K) t (h _ a.1.2)
    (isIntegral_A₀_of t (isIntegral_of_mem_coordRing t a))⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' _ _ := Subtype.ext (Subtype.ext (by simp))
  map_zero' := Subtype.ext (Subtype.ext (by simp))
  map_add' _ _ := Subtype.ext (Subtype.ext (by simp))

@[simp] lemma coe_bcMap {F : IntermediateField (K₀ k t) Ω} {F' : IntermediateField (K₀ K t) Ω}
    (h : ∀ x ∈ F, x ∈ F') (a : coordRing k t F) :
    (((bcMap h a : coordRing K t F') : F') : Ω) = ((a : F) : Ω) := rfl

lemma bcMap_injective {F : IntermediateField (K₀ k t) Ω} {F' : IntermediateField (K₀ K t) Ω}
    (h : ∀ x ∈ F, x ∈ F') : Function.Injective (bcMap h) := fun a b hab =>
  Subtype.ext (Subtype.ext (congrArg (fun c : coordRing K t F' => ((c : F') : Ω)) hab))

/-- `bcMap` commutes with the inclusions. -/
lemma bcMap_comp_ringMap {F₁ F₂ : IntermediateField (K₀ k t) Ω}
    {F₁' F₂' : IntermediateField (K₀ K t) Ω} (h₁ : ∀ x ∈ F₁, x ∈ F₁') (h₂ : ∀ x ∈ F₂, x ∈ F₂')
    (h : F₁ ≤ F₂) (h' : F₁' ≤ F₂') :
    (ringMap t h').toRingHom.comp (bcMap h₁) = (bcMap h₂).comp (ringMap t h).toRingHom :=
  RingHom.ext fun _ => rfl

/-- Evaluation of polynomials over `k(t)` at elements of an intermediate field over `K(t)`. -/
lemma coe_aeval_map (F' : IntermediateField (K₀ K t) Ω) (q : (K₀ k t)[X]) (z : F') :
    ((aeval z (q.map (K₀Map (K := K) t)) : F') : Ω) = aeval (z : Ω) q := by
  have h1 : ((aeval z (q.map (K₀Map (K := K) t)) : F') : Ω) =
      aeval (algebraMap F' Ω z) (q.map (K₀Map (K := K) t)) :=
    (Polynomial.aeval_algebraMap_apply Ω z _).symm
  rw [h1, aeval_def, eval₂_map, aeval_def]
  rfl

lemma transcendental_of_bc (htK : Transcendental K t) : Transcendental k t := by
  intro h
  exact htK (h.extendScalars (algebraMap k K).injective)

end Basic

section Unramified

open UniqueFactorizationMonoid

/-- In a Dedekind domain, `p S ⊆ P ^ n` bounds the ramification index from below. -/
lemma le_ramificationIdx'_of_le_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain S] {p : Ideal R} {P : Ideal S} (hp0 : p.map (algebraMap R S) ≠ ⊥)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) {n : ℕ} (h : p.map (algebraMap R S) ≤ P ^ n) :
    n ≤ p.ramificationIdx' P := by
  classical
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]
  have hdvd : P ^ n ∣ p.map (algebraMap R S) := Ideal.dvd_iff_le.mpr h
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0,
    normalizedFactors_pow, normalizedFactors_irreducible hPirr, normalize_eq,
    Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le] at hdvd
  exact hdvd

/-- **Ramification indices do not drop under an unramified extension of the base**: for a
commutative square `R → S`, `R' → S'` (`α : R → R'`, `β : S → S'`) of extensions of Dedekind
domains, `R'` principal, a nonzero prime `u'` of `S'` with `u = β⁻¹(u') ≠ 0`, if some element of
`p = u ∩ R` is not in `(u' ∩ R')²`, then `e(u | p) ≤ e(u' | p')`. -/
lemma ramificationIdx_le_of_square {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] [IsDomain R] [IsDomain R'] [IsDedekindDomain S] [IsDedekindDomain S']
    [IsPrincipalIdealRing R'] [Algebra R S] [Algebra R' S'] [Module.IsTorsionFree R S]
    [Module.IsTorsionFree R' S'] [Algebra.IsIntegral R S]
    (α : R →+* R') (β : S →+* S') (hβ : Function.Injective β)
    (hcomm : ∀ r, β (algebraMap R S r) = algebraMap R' S' (α r))
    (u' : Ideal S') [hu' : u'.IsPrime] (hu : u'.comap β ≠ ⊥)
    (hsq : ∃ a ∈ (u'.comap β).under R, α a ∉ (u'.under R') ^ 2) :
    (u'.comap β).ramificationIdx R ≤ u'.ramificationIdx R' := by
  classical
  set u := u'.comap β with hu_def
  haveI : u.IsPrime := Ideal.comap_isPrime β u'
  set p := u.under R
  set p' := u'.under R'
  obtain ⟨a, ha, hap⟩ := hsq
  have hau : algebraMap R S a ∈ u := ha
  have hap' : α a ∈ p' := by
    change algebraMap R' S' (α a) ∈ u'
    rw [← hcomm]; exact hau
  have hp'0 : p' ≠ ⊥ := by
    rintro h
    apply hap
    rw [h] at hap' ⊢
    rw [Ideal.mem_bot] at hap'
    rw [hap']; exact zero_mem _
  have hu'0 : u' ≠ ⊥ := by
    rintro rfl
    apply hp'0
    rw [eq_bot_iff]
    intro x hx
    have : algebraMap R' S' x = 0 := (Ideal.mem_bot).mp hx
    exact (Ideal.mem_bot).mpr ((Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)
      (this.trans (map_zero _).symm))
  have hp0 : p ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hu
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  haveI : u.LiesOver p := ⟨rfl⟩
  haveI : u'.LiesOver p' := ⟨rfl⟩
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx p u hp0,
    ← Ideal.ramificationIdx'_eq_ramificationIdx p' u' hp'0]
  set e := p.ramificationIdx' u
  -- `β(a) ∈ u'^e`
  have h1 : algebraMap R S a ∈ u ^ e :=
    Ideal.le_pow_ramificationIdx' (p := p) (P := u) (Ideal.mem_map_of_mem _ ha)
  have h2 : algebraMap R' S' (α a) ∈ u' ^ e := by
    rw [← hcomm]
    have : Ideal.map β (u ^ e) ≤ u' ^ e := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr le_rfl) e
    exact this (Ideal.mem_map_of_mem β h1)
  -- `α(a) = g r` with `p' = (g)`, `r ∉ p'`
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal p').principal
  have hg' : p' = Ideal.span {g} := hg
  have hga : g ∣ α a := by
    rw [← Ideal.mem_span_singleton, ← hg']; exact hap'
  obtain ⟨r, hr⟩ := hga
  have hr' : r ∉ p' := by
    intro hrp
    apply hap
    rw [hg', Ideal.span_singleton_pow, Ideal.mem_span_singleton, hr, pow_two]
    rw [hg', Ideal.mem_span_singleton] at hrp
    exact mul_dvd_mul_left g hrp
  have h3 : algebraMap R' S' g ∈ u' ^ e := by
    have : algebraMap R' S' r * algebraMap R' S' g ∈ u' ^ e := by
      rw [← map_mul, mul_comm, ← hr]; exact h2
    exact (Ideal.IsPrime.mul_mem_pow u' this).resolve_left hr'
  have hmap : p'.map (algebraMap R' S') ≤ u' ^ e := by
    rw [hg', Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact h3
  have hmap0 : p'.map (algebraMap R' S') ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp'0
  exact le_ramificationIdx'_of_le_pow hmap0 hu' hu'0 hmap

end Unramified

section Line

variable {t}

lemma bot_mem_bc : ∀ x ∈ (⊥ : IntermediateField (K₀ k t) Ω),
    x ∈ (⊥ : IntermediateField (K₀ K t) Ω) := by
  intro x hx
  obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact IntermediateField.mem_bot.mpr ⟨K₀Map t c, rfl⟩

lemma bcMap_coordRingBotEquiv (htk : Transcendental k t) (htK : Transcendental K t) (q : k[X]) :
    bcMap (bot_mem_bc (k := k) (K := K) (t := t)) (coordRingBotEquiv htk q) = coordRingBotEquiv htK (q.map (algebraMap k K)) := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_bcMap, coe_coordRingBotEquiv, coe_coordRingBotEquiv, Polynomial.aeval_map_algebraMap]

/-- **`k[t] → K[t]` is unramified** (characteristic `0`): for a nonzero prime `v'` of `K[t]` over
the nonzero prime `v` of `k[t]`, some element of `v` is not in `v'²`. -/
lemma exists_mem_not_mem_sq [CharZero k] (htk : Transcendental k t) (htK : Transcendental K t)
    (v' : Ideal (coordRing K t (⊥ : IntermediateField (K₀ K t) Ω))) [hv' : v'.IsPrime]
    (hv'0 : v' ≠ ⊥) (hv0 : v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t))) ≠ ⊥) :
    ∃ a ∈ v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t))), bcMap (bot_mem_bc (k := k) (K := K) (t := t)) a ∉ v' ^ 2 := by
  classical
  set ek := coordRingBotEquiv (Ω := Ω) htk
  set eK := coordRingBotEquiv (Ω := Ω) htK
  set v := v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t)))
  haveI : v.IsPrime := Ideal.comap_isPrime _ _
  let Q : Ideal k[X] := v.comap ek.toRingEquiv.toRingHom
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hv0
    rw [eq_bot_iff]
    intro x hx
    have : ek.symm x ∈ Q := by
      change ek (ek.symm x) ∈ v
      rw [AlgEquiv.apply_symm_apply]; exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← ek.apply_symm_apply x, this, map_zero]
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal Q).principal
  have hQπ : Q = Ideal.span {π} := hπ
  have hπprime : Prime π := by
    rw [← Ideal.span_singleton_prime (fun h => hQ0 (by rw [hQπ, h, Ideal.span_singleton_eq_bot.mpr rfl])),
      ← hQπ]
    infer_instance
  have hsq : Squarefree (π.map (algebraMap k K)) :=
    ((hπprime.irreducible.separable).map).squarefree
  refine ⟨ek π, ?_, ?_⟩
  · change π ∈ Q
    rw [hQπ]; exact Ideal.mem_span_singleton_self π
  · intro hmem
    rw [bcMap_coordRingBotEquiv htk htK] at hmem
    let Q' : Ideal K[X] := v'.comap eK.toRingEquiv.toRingHom
    haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal Q').principal
    have hQ'q : Q' = Ideal.span {q} := hq
    have hv'q : v' = Ideal.span {eK q} := by
      ext x
      rw [Ideal.mem_span_singleton, ← eK.apply_symm_apply x, map_dvd_iff eK]
      exact (show eK.symm x ∈ Q' ↔ _ by rw [hQ'q, Ideal.mem_span_singleton])
    rw [hv'q, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow, map_dvd_iff eK,
      pow_two] at hmem
    have hunit := hsq q hmem
    apply (show Q' ≠ ⊤ from Ideal.IsPrime.ne_top inferInstance)
    rw [hQ'q, Ideal.span_singleton_eq_top]
    exact hunit

end Line

section Res

variable {t} {N : IntermediateField (K₀ k t) Ω} {N' : IntermediateField (K₀ K t) Ω}
  (hN : ∀ x ∈ N, x ∈ N')

/-- Automorphisms of `N'` over `K(t)` preserve the normal extension `N` of `k(t)`. -/
lemma mem_of_aut [Normal (K₀ k t) N] (σ' : N' ≃ₐ[K₀ K t] N') (x : N') (hx : (x : Ω) ∈ N) :
    ((σ' x : N') : Ω) ∈ N := by
  set q := minpoly (K₀ k t) (x : Ω)
  have hint : IsIntegral (K₀ k t) (x : Ω) := by
    have := Normal.isIntegral (F := K₀ k t) (K := N) inferInstance ⟨x, hx⟩
    exact this.map (IsScalarTower.toAlgHom (K₀ k t) N Ω)
  have hq0 : q ≠ 0 := minpoly.ne_zero hint
  have hq : aeval (x : Ω) q = 0 := minpoly.aeval _ _
  have h1 : aeval x (q.map (K₀Map (K := K) t)) = 0 := by
    apply Subtype.ext
    rw [coe_aeval_map, hq]; rfl
  have h2 : aeval (σ' x) (q.map (K₀Map (K := K) t)) = 0 := by
    rw [Polynomial.aeval_algHom_apply σ', h1, map_zero]
  have h3 : aeval ((σ' x : N') : Ω) q = 0 := by
    rw [← coe_aeval_map, h2]; rfl
  have hsplit : (q.map (algebraMap (K₀ k t) N)).Splits := by
    have := Normal.splits (F := K₀ k t) (K := N) inferInstance ⟨x, hx⟩
    rwa [IntermediateField.minpoly_eq] at this
  have hroot : ((q.map (algebraMap (K₀ k t) N)).map (algebraMap N Ω)).IsRoot ((σ' x : N') : Ω) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.IsRoot, eval_map,
      ← aeval_def]
    exact h3
  obtain ⟨y, hy⟩ := hsplit.mem_range_of_isRoot (Polynomial.map_ne_zero hq0) hroot
  rw [← hy]
  exact y.2

variable [Normal (K₀ k t) N]

/-- The restriction of an automorphism of `N'` to `N`, as a function. -/
noncomputable def resFun (σ' : N' ≃ₐ[K₀ K t] N') (x : N) : N :=
  ⟨σ' ⟨x, hN x x.2⟩, mem_of_aut σ' _ x.2⟩

@[simp] lemma coe_resFun (σ' : N' ≃ₐ[K₀ K t] N') (x : N) :
    ((resFun hN σ' x : N) : Ω) = ((σ' ⟨x, hN x x.2⟩ : N') : Ω) := rfl

/-- **Restriction** `Gal(N' / K(t)) → Gal(N / k(t))`. -/
noncomputable def res : (N' ≃ₐ[K₀ K t] N') →* (N ≃ₐ[K₀ k t] N) where
  toFun σ' :=
    { toFun := resFun hN σ'
      invFun := resFun hN σ'.symm
      left_inv x := Subtype.ext (by
        simp only [coe_resFun]
        have : (⟨((σ' ⟨x, hN x x.2⟩ : N') : Ω), hN _ (mem_of_aut σ' _ x.2)⟩ : N') =
            σ' ⟨x, hN x x.2⟩ := rfl
        rw [this, AlgEquiv.symm_apply_apply])
      right_inv x := Subtype.ext (by
        simp only [coe_resFun]
        have : (⟨((σ'.symm ⟨x, hN x x.2⟩ : N') : Ω), hN _ (mem_of_aut σ'.symm _ x.2)⟩ : N') =
            σ'.symm ⟨x, hN x x.2⟩ := rfl
        rw [this, AlgEquiv.apply_symm_apply])
      map_mul' x y := Subtype.ext (by
        change ((σ' (⟨x, hN x x.2⟩ * ⟨y, hN y y.2⟩) : N') : Ω) = _
        rw [map_mul]; rfl)
      map_add' x y := Subtype.ext (by
        change ((σ' (⟨x, hN x x.2⟩ + ⟨y, hN y y.2⟩) : N') : Ω) = _
        rw [map_add]; rfl)
      commutes' c := Subtype.ext (by
        simp only [coe_resFun]
        have : (⟨((algebraMap (K₀ k t) N c : N) : Ω), hN _ (algebraMap (K₀ k t) N c).2⟩ : N') =
            algebraMap (K₀ K t) N' (K₀Map t c) := rfl
        rw [this, AlgEquiv.commutes]; rfl) }
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp] lemma coe_res_apply (σ' : N' ≃ₐ[K₀ K t] N') (x : N) :
    ((res hN σ' x : N) : Ω) = ((σ' ⟨x, hN x x.2⟩ : N') : Ω) := rfl

include hN in
/-- An automorphism of `N' = K(t) · N` fixing `N` is trivial. -/
lemma eq_of_fix (hN' : N' ≤ IntermediateField.adjoin (K₀ K t) (N : Set Ω))
    (σ' : N' ≃ₐ[K₀ K t] N') (h : ∀ x : N', (x : Ω) ∈ N → σ' x = x) : σ' = 1 := by
  let S : IntermediateField (K₀ K t) Ω :=
    (IntermediateField.fixedField (Subgroup.zpowers σ')).map N'.val
  have hS : IntermediateField.adjoin (K₀ K t) (N : Set Ω) ≤ S := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    refine ⟨⟨y, hN y hy⟩, ?_, rfl⟩
    rintro ⟨τ, n, rfl⟩
    change (σ' ^ n) _ = _
    induction n using Int.induction_on with
    | zero => rfl
    | succ n ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, h _ hy]; exact ih
    | pred n ih =>
      rw [zpow_sub_one, AlgEquiv.mul_apply]
      have : σ'⁻¹ ⟨y, hN y hy⟩ = ⟨y, hN y hy⟩ := by
        conv_lhs => rw [← h ⟨y, hN y hy⟩ hy]
        exact σ'.symm_apply_apply _
      rw [this]; exact ih
  ext x
  obtain ⟨z, hz, hzx⟩ := hS (hN' x.2)
  have : z = x := Subtype.ext hzx
  subst this
  exact congrArg Subtype.val
    ((IntermediateField.mem_fixedField_iff _ _).mp hz σ' (Subgroup.mem_zpowers σ'))

lemma res_injective (hN' : N' ≤ IntermediateField.adjoin (K₀ K t) (N : Set Ω)) :
    Function.Injective (res hN) := by
  rw [injective_iff_map_eq_one]
  intro σ' h1
  refine eq_of_fix hN hN' σ' fun x hx => ?_
  have := congrArg (fun τ : N ≃ₐ[K₀ k t] N => ((τ ⟨x, hx⟩ : N) : Ω)) h1
  exact Subtype.ext this

end Res

section Inertia

variable {t} {N : IntermediateField (K₀ k t) Ω} {N' : IntermediateField (K₀ K t) Ω}
  (hN : ∀ x ∈ N, x ∈ N') [Normal (K₀ k t) N] [FiniteDimensional (K₀ k t) N]

set_option synthInstance.maxHeartbeats 400000 in
lemma bcMap_smul (σ' : N' ≃ₐ[K₀ K t] N') (x : coordRing k t N) :
    bcMap hN (res hN σ' • x) = σ' • bcMap hN x := rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- **Restriction maps inertia groups to inertia groups.** -/
lemma res_mem_inertia (u' : Ideal (coordRing K t N')) (σ' : N' ≃ₐ[K₀ K t] N')
    (hσ : σ' ∈ u'.inertia (N' ≃ₐ[K₀ K t] N')) :
    res hN σ' ∈ (u'.comap (bcMap hN)).inertia (N ≃ₐ[K₀ k t] N) := by
  intro x
  change bcMap hN (res hN σ' • x - x) ∈ u'
  rw [map_sub, bcMap_smul]
  exact hσ _

set_option synthInstance.maxHeartbeats 400000 in
/-- If `u' ∩ coordRing N = 0`, the inertia group of `u'` is trivial. -/
lemma inertia_eq_bot (hN' : N' ≤ IntermediateField.adjoin (K₀ K t) (N : Set Ω))
    (u' : Ideal (coordRing K t N')) (hu : u'.comap (bcMap hN) = ⊥) (σ' : N' ≃ₐ[K₀ K t] N')
    (hσ : σ' ∈ u'.inertia (N' ≃ₐ[K₀ K t] N')) : σ' = 1 := by
  have h := res_mem_inertia hN u' σ' hσ
  rw [hu] at h
  have hres : res hN σ' = 1 := by
    haveI := faithfulSMul_coordRing (k := k) t (N := N)
    apply FaithfulSMul.eq_of_smul_eq_smul (α := coordRing k t N)
    intro x
    have h0 : res hN σ' • x - x = 0 := by simpa using h x
    rw [sub_eq_zero] at h0
    rw [h0, one_smul]
  exact res_injective hN hN' (hres.trans (map_one _).symm)

variable [CharZero k] (htK : Transcendental K t) [IsGalois (K₀ k t) N]
  [FiniteDimensional (K₀ K t) N'] [IsGalois (K₀ K t) N']

omit [Normal (K₀ k t) N] [IsGalois (K₀ k t) N] in
lemma isPrincipalIdealRing_coordRing_bot (ht : Transcendental K t) :
    IsPrincipalIdealRing (coordRing K t (⊥ : IntermediateField (K₀ K t) Ω)) :=
  IsPrincipalIdealRing.of_surjective (coordRingBotEquiv ht).toRingEquiv.toRingHom
    (coordRingBotEquiv ht).surjective

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
include htK in
/-- `|I_u| ≤ |I_{u'}|` for `u = u' ∩ coordRing N ≠ 0`. -/
lemma card_inertia_le (u' : Ideal (coordRing K t N')) [hu' : u'.IsMaximal]
    (hu : u'.comap (bcMap hN) ≠ ⊥) :
    Nat.card ((u'.comap (bcMap hN)).inertia (N ≃ₐ[K₀ k t] N)) ≤
      Nat.card (u'.inertia (N' ≃ₐ[K₀ K t] N')) := by
  have htk : Transcendental k t := transcendental_of_bc (K := K) htK
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  set u := u'.comap (bcMap hN)
  haveI : u.IsPrime := Ideal.comap_isPrime _ _
  haveI := isDedekindDomain_ring t htk N
  haveI := isDedekindDomain_ring t htK N'
  haveI hum : u.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hu
  have e1 := ramificationIdx_eq_card_inertia t htk (bot_le : ⊥ ≤ N) u
  have e2 := ramificationIdx_eq_card_inertia t htK (bot_le : ⊥ ≤ N') u'
  rw [fixSub_bot, inf_top_eq] at e1 e2
  rw [← e1, ← e2]
  letI := algRing t (bot_le : ⊥ ≤ N)
  letI := algRing t (bot_le : ⊥ ≤ N')
  haveI := isPrincipalIdealRing_coordRing_bot htK
  haveI : Module.IsTorsionFree (coordRing k t (⊥ : IntermediateField (K₀ k t) Ω))
      (coordRing k t N) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact ringMap_injective t _
  haveI : Module.IsTorsionFree (coordRing K t (⊥ : IntermediateField (K₀ K t) Ω))
      (coordRing K t N') := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact ringMap_injective t _
  haveI : Algebra.IsIntegral (coordRing k t (⊥ : IntermediateField (K₀ k t) Ω))
      (coordRing k t N) := ⟨ringMap_isIntegral t _⟩
  refine ramificationIdx_le_of_square (bcMap (bot_mem_bc (k := k) (K := K) (t := t)))
    (bcMap hN) (bcMap_injective hN) (fun _ => rfl) u' hu ?_
  set v' := u'.under (coordRing K t (⊥ : IntermediateField (K₀ K t) Ω))
  haveI : v'.IsPrime := Ideal.comap_isPrime _ _
  have hcomap : u.under (coordRing k t (⊥ : IntermediateField (K₀ k t) Ω)) =
      v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t))) := rfl
  have hv0 : v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t))) ≠ ⊥ := by
    rw [← hcomap]
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hu
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  have hv'0 : v' ≠ ⊥ := by
    intro h
    apply hv0
    rw [h, eq_bot_iff]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    rw [Ideal.mem_bot]
    exact bcMap_injective _ (hx.trans (map_zero _).symm)
  rw [hcomap]
  exact exists_mem_not_mem_sq htk htK v' hv'0 hv0

end Inertia

end AffOrbicurve
