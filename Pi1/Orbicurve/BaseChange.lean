module

public import Pi1.Orbicurve.CoreCriterion
public import Pi1.Orbicurve.ValuationInertia
public import Mathlib.LinearAlgebra.Lagrange

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
open scoped Pointwise

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
    (h : ∀ x ∈ F, x ∈ F') : Function.Injective (bcMap h) := fun _ _ hab =>
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

set_option linter.unusedVariables false in
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
    bcMap (bot_mem_bc (k := k) (K := K) (t := t)) (coordRingBotEquiv htk q) =
      coordRingBotEquiv htK (q.map (algebraMap k K)) := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_bcMap, coe_coordRingBotEquiv, coe_coordRingBotEquiv, Polynomial.aeval_map_algebraMap]

set_option linter.unusedVariables false in
/-- **`k[t] → K[t]` is unramified** (characteristic `0`): for a nonzero prime `v'` of `K[t]` over
the nonzero prime `v` of `k[t]`, some element of `v` is not in `v'²`. -/
lemma exists_mem_not_mem_sq [CharZero k] (htk : Transcendental k t) (htK : Transcendental K t)
    (v' : Ideal (coordRing K t (⊥ : IntermediateField (K₀ K t) Ω))) [hv' : v'.IsPrime]
    (hv'0 : v' ≠ ⊥) (hv0 : v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t))) ≠ ⊥) :
    ∃ a ∈ v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t))),
      bcMap (bot_mem_bc (k := k) (K := K) (t := t)) a ∉ v' ^ 2 := by
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
    rw [← Ideal.span_singleton_prime
      (fun h => hQ0 (by rw [hQπ, h, Ideal.span_singleton_eq_bot.mpr rfl])),
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
set_option linter.unusedSectionVars false in
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
set_option linter.unusedSectionVars false in
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

omit [Normal (K₀ k t) N] [FiniteDimensional (K₀ k t) N] [CharZero k] [IsGalois (K₀ k t) N]
  [FiniteDimensional (K₀ K t) N'] [IsGalois (K₀ K t) N'] in
/-- An automorphism of `N'` over `K(t)` fixing `S` fixes `K(t)(S)`. -/
lemma fix_adjoin (σ' : N' ≃ₐ[K₀ K t] N') {S : Set Ω} (hS : ∀ x ∈ S, x ∈ N')
    (h : ∀ x : N', (x : Ω) ∈ S → σ' x = x) (x : N')
    (hx : (x : Ω) ∈ IntermediateField.adjoin (K₀ K t) S) : σ' x = x := by
  let T : IntermediateField (K₀ K t) Ω :=
    (IntermediateField.fixedField (Subgroup.zpowers σ')).map N'.val
  have hT : IntermediateField.adjoin (K₀ K t) S ≤ T := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    refine ⟨⟨y, hS y hy⟩, ?_, rfl⟩
    rintro ⟨τ, n, rfl⟩
    change (σ' ^ n) _ = _
    induction n using Int.induction_on with
    | zero => rfl
    | succ n ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, h _ hy]; exact ih
    | pred n ih =>
      rw [zpow_sub_one, AlgEquiv.mul_apply]
      have : σ'⁻¹ ⟨y, hS y hy⟩ = ⟨y, hS y hy⟩ := by
        conv_lhs => rw [← h ⟨y, hS y hy⟩ hy]
        exact σ'.symm_apply_apply _
      rw [this]; exact ih
  obtain ⟨z, hz, hzx⟩ := hT hx
  have : z = x := Subtype.ext hzx
  subst this
  exact (IntermediateField.mem_fixedField_iff _ _).mp hz σ' (Subgroup.mem_zpowers σ')

omit [FiniteDimensional (K₀ k t) N] [CharZero k] [IsGalois (K₀ k t) N]
  [FiniteDimensional (K₀ K t) N'] [IsGalois (K₀ K t) N'] in
/-- `Gal(N' / F') = res⁻¹ Gal(N / F)` for `F' = K(t) · F`. -/
lemma mem_fixSub_iff_res {F : IntermediateField (K₀ k t) Ω} {F' : IntermediateField (K₀ K t) Ω}
    (hFN : F ≤ N) (hF : ∀ x ∈ F, x ∈ F') (hF' : F' ≤ IntermediateField.adjoin (K₀ K t) (F : Set Ω))
    (σ' : N' ≃ₐ[K₀ K t] N') : σ' ∈ fixSub t N' F' ↔ res hN σ' ∈ fixSub t N F := by
  constructor
  · intro h x hx
    apply Subtype.ext
    rw [coe_res_apply]
    exact congrArg Subtype.val (h ⟨x, hN x x.2⟩ (hF _ hx))
  · intro h x hx
    refine fix_adjoin σ' (fun y hy => hN y (hFN hy)) (fun y hy => ?_) x (hF' hx)
    have := congrArg Subtype.val (h ⟨y, hFN hy⟩ hy)
    rw [coe_res_apply] at this
    exact Subtype.ext this

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
include htK in
/-- **Restriction identifies the inertia groups** `I_{u'} ≅ I_{u' ∩ N}` (for `u' ∩ N ≠ 0`). -/
lemma map_res_inertia (hN' : N' ≤ IntermediateField.adjoin (K₀ K t) (N : Set Ω))
    (u' : Ideal (coordRing K t N')) [u'.IsMaximal] (hu : u'.comap (bcMap hN) ≠ ⊥) :
    (u'.inertia (N' ≃ₐ[K₀ K t] N')).map (res hN) =
      (u'.comap (bcMap hN)).inertia (N ≃ₐ[K₀ k t] N) := by
  have hle : (u'.inertia (N' ≃ₐ[K₀ K t] N')).map (res hN) ≤
      (u'.comap (bcMap hN)).inertia (N ≃ₐ[K₀ k t] N) := by
    rintro _ ⟨σ', hσ', rfl⟩
    exact res_mem_inertia hN u' σ' hσ'
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (res_injective hN hN')]
  exact card_inertia_le hN htK u' hu

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
include htK in
lemma card_inertia_inf_fixSub (hN' : N' ≤ IntermediateField.adjoin (K₀ K t) (N : Set Ω))
    {F : IntermediateField (K₀ k t) Ω} {F' : IntermediateField (K₀ K t) Ω}
    (hFN : F ≤ N) (hF : ∀ x ∈ F, x ∈ F') (hF' : F' ≤ IntermediateField.adjoin (K₀ K t) (F : Set Ω))
    (u' : Ideal (coordRing K t N')) [u'.IsMaximal] (hu : u'.comap (bcMap hN) ≠ ⊥) :
    Nat.card (u'.inertia (N' ≃ₐ[K₀ K t] N') ⊓ fixSub t N' F' : Subgroup _) =
      Nat.card ((u'.comap (bcMap hN)).inertia (N ≃ₐ[K₀ k t] N) ⊓ fixSub t N F : Subgroup _) := by
  rw [← Subgroup.card_map_of_injective (res_injective hN hN')]
  have hmap : (u'.inertia (N' ≃ₐ[K₀ K t] N') ⊓ fixSub t N' F' : Subgroup _).map (res hN) =
      (u'.comap (bcMap hN)).inertia (N ≃ₐ[K₀ k t] N) ⊓ fixSub t N F := by
    rw [← map_res_inertia hN htK hN' u' hu]
    ext τ
    simp only [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨σ', ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨σ', h1, rfl⟩, (mem_fixSub_iff_res hN hFN hF hF' σ').mp h2⟩
    · rintro ⟨⟨σ', h1, rfl⟩, h2⟩
      exact ⟨σ', ⟨h1, (mem_fixSub_iff_res hN hFN hF hF' σ').mpr h2⟩, rfl⟩
  rw [hmap]

end Inertia

section AlgClosed

omit [Algebra k Ω] [IsScalarTower k K Ω] [Algebra K Ω] in
/-- An element of `K` integral over the algebraically closed subfield `k` lies in `k`. -/
lemma mem_range_of_isIntegral [IsAlgClosed k] {y : K} (hy : IsIntegral k y) :
    y ∈ (algebraMap k K).range := by
  refine ⟨-(minpoly k y).coeff 0, ?_⟩
  have hq : (minpoly k y).leadingCoeff = 1 := minpoly.monic hy
  have h : (minpoly k y).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hy)
  have : aeval y (minpoly k y) = 0 := minpoly.aeval k y
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact (map_neg (algebraMap k K) ((minpoly k y).coeff 0)).symm ▸ this.symm

omit [Algebra k Ω] [IsScalarTower k K Ω] [Algebra K Ω] in
/-- **Interpolation**: a polynomial over `K` taking values in the infinite subfield `k` at all
points of `k` has coefficients in `k`. -/
lemma exists_map_eq_of_eval_mem [Infinite k] (P : K[X])
    (hP : ∀ c : k, P.eval (algebraMap k K c) ∈ (algebraMap k K).range) :
    ∃ Q : k[X], Q.map (algebraMap k K) = P := by
  classical
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq k (P.natDegree + 1)
  let v : k → k := fun c => (hP c).choose
  have hv : ∀ c, algebraMap k K (v c) = P.eval (algebraMap k K c) := fun c => (hP c).choose_spec
  let Q := Lagrange.interpolate s id v
  refine ⟨Q, ?_⟩
  let s' : Finset K := s.map ⟨algebraMap k K, (algebraMap k K).injective⟩
  have hs' : s'.card = P.natDegree + 1 := by rw [Finset.card_map, hs]
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq s'
  · rw [hs']
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · rw [Polynomial.degree_map]
      have := Lagrange.degree_interpolate_lt (s := s) (v := id) v (Set.injOn_id _)
      rw [hs] at this
      exact_mod_cast this
    · exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self _)
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hx
    change eval (algebraMap k K c) (Q.map (algebraMap k K)) = eval (algebraMap k K c) P
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply, ← hv]
    congr 1
    exact Lagrange.eval_interpolate_at_node (v := id) v (Set.injOn_id _) hc

variable {t}

lemma coe_algEquivOfTranscendental {F : Type u} [Field F] [Algebra F Ω] (ht : Transcendental F t)
    (P : F[X]) : ((Polynomial.algEquivOfTranscendental F t ht P : A₀ F t) : Ω) = aeval t P := by
  change ((aeval (⟨t, Algebra.self_mem_adjoin_singleton F t⟩ : A₀ F t) P : A₀ F t) : Ω) = _
  rw [← Subalgebra.aeval_coe]

variable [IsAlgClosed k]

set_option maxHeartbeats 1000000 in
/-- **`K(t) ∩ \overline{k(t)} = k(t)`** for `k` algebraically closed. -/
theorem mem_K₀_of_isAlgebraic (htK : Transcendental K t) {x : Ω} (hx : x ∈ K₀ K t)
    (halg : IsAlgebraic (K₀ k t) x) : x ∈ K₀ k t := by
  classical
  have htk : Transcendental k t := transcendental_of_bc (K := K) htK
  haveI : Infinite k := IsAlgClosed.instInfinite
  haveI := isPrincipalIdealRing_A₀ htK
  have halg' : IsAlgebraic (A₀ k t) x :=
    (IsFractionRing.isAlgebraic_iff (A₀ k t) (K₀ k t) Ω).mpr halg
  obtain ⟨y, hy0, hyint⟩ := halg'.exists_integral_multiple
  have hyK₀ : (y : Ω) ∈ K₀ k t :=
    (Algebra.adjoin_le_iff.mpr (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]; exact IntermediateField.mem_adjoin_simple_self k t) :
      A₀ k t ≤ (K₀ k t).toSubalgebra) y.2
  set g : Ω := (y : Ω) * x with hg
  have hgint : IsIntegral (A₀ k t) g := by
    rw [hg]; exact hyint
  have hgK : g ∈ K₀ K t := mul_mem (K₀_le_bc t hyK₀) hx
  set eK := Polynomial.algEquivOfTranscendental K t htK
  set ek := Polynomial.algEquivOfTranscendental k t htk
  -- `g = P(t)` with `P ∈ K[X]`
  obtain ⟨P, hP⟩ : ∃ P : K[X], aeval t P = g := by
    have h1 : IsIntegral (A₀ K t) (⟨g, hgK⟩ : K₀ K t) := by
      haveI : IsScalarTower (A₀ K t) (K₀ K t) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact (isIntegral_algebraMap_iff (algebraMap (K₀ K t) Ω).injective).mp
        (isIntegral_A₀_of t hgint)
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A₀ K t) (K := K₀ K t)).mp h1
    refine ⟨eK.symm a, ?_⟩
    rw [← coe_algEquivOfTranscendental htK, AlgEquiv.apply_symm_apply]
    exact congrArg Subtype.val ha
  -- the integral equation, over `K[X]`
  obtain ⟨f, hfm, hf⟩ := hgint
  let ρ : A₀ k t →+* K[X] :=
    (Polynomial.mapRingHom (algebraMap k K)).comp ek.symm.toRingEquiv.toRingHom
  have hρ : (aeval t : K[X] →ₐ[K] Ω).toRingHom.comp ρ = algebraMap (A₀ k t) Ω := by
    ext a
    obtain ⟨q, rfl⟩ := ek.surjective a
    change aeval t ((ek.symm (ek q)).map (algebraMap k K)) = ((ek q : A₀ k t) : Ω)
    rw [AlgEquiv.symm_apply_apply, Polynomial.aeval_map_algebraMap, coe_algEquivOfTranscendental]
  have hPf : Polynomial.eval₂ ρ P f = 0 := by
    apply (transcendental_iff_injective.mp htK)
    rw [map_zero]
    have := Polynomial.hom_eval₂ f ρ (aeval t : K[X] →ₐ[K] Ω).toRingHom P
    change (aeval t : K[X] →ₐ[K] Ω).toRingHom (Polynomial.eval₂ ρ P f) = 0
    rw [this, hρ]
    change Polynomial.eval₂ (algebraMap (A₀ k t) Ω) (aeval t P) f = 0
    rw [hP]; exact hf
  have hPc : ∀ c : k, P.eval (algebraMap k K c) ∈ (algebraMap k K).range := by
    intro c
    apply mem_range_of_isIntegral
    let φ : A₀ k t →+* k := (Polynomial.evalRingHom c).comp ek.symm.toRingEquiv.toRingHom
    refine ⟨f.map φ, hfm.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap k K).comp φ =
        (Polynomial.evalRingHom (algebraMap k K c)).comp ρ := by
      ext a
      obtain ⟨q, rfl⟩ := ek.surjective a
      change algebraMap k K ((ek.symm (ek q)).eval c) =
        ((ek.symm (ek q)).map (algebraMap k K)).eval (algebraMap k K c)
      rw [AlgEquiv.symm_apply_apply, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [hc]
    change Polynomial.eval₂ _ ((Polynomial.evalRingHom (algebraMap k K c)) P) f = 0
    rw [← Polynomial.hom_eval₂, hPf, map_zero]
  obtain ⟨Q, rfl⟩ := exists_map_eq_of_eval_mem P hPc
  have hgk : g ∈ K₀ k t := by
    rw [← hP, Polynomial.aeval_map_algebraMap, ← coe_algEquivOfTranscendental htk]
    exact (Algebra.adjoin_le_iff.mpr (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]; exact IntermediateField.mem_adjoin_simple_self k t) :
      A₀ k t ≤ (K₀ k t).toSubalgebra) (ek Q).2
  have hy : (y : Ω) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hxg : x = g / (y : Ω) := by
    rw [hg]; field_simp
  rw [hxg]
  exact div_mem hgk hyK₀

end AlgClosed

section Closure

variable {t} [IsAlgClosed Ω] [CharZero k]

set_option linter.unusedSectionVars false in
lemma rootSet_map_K₀Map (p : (K₀ k t)[X]) :
    (p.map (K₀Map (K := K) t)).rootSet Ω = p.rootSet Ω := by
  classical
  rw [Polynomial.rootSet_def, Polynomial.rootSet_def, Polynomial.aroots_def,
    Polynomial.aroots_def, Polynomial.map_map]
  rfl

set_option linter.unusedVariables false in
/-- **Galois closures and their base changes**: every finite extension `F` of `k(t)` in `Ω` lies in
a finite Galois extension `N` of `k(t)` whose compositum `N' = K(t) · N` is finite Galois over
`K(t)`. -/
theorem exists_galois_bc (htK : Transcendental K t) (F : IntermediateField (K₀ k t) Ω)
    [FiniteDimensional (K₀ k t) F] :
    ∃ (N : IntermediateField (K₀ k t) Ω) (N' : IntermediateField (K₀ K t) Ω),
      F ≤ N ∧ FiniteDimensional (K₀ k t) N ∧ IsGalois (K₀ k t) N ∧
      FiniteDimensional (K₀ K t) N' ∧ IsGalois (K₀ K t) N' ∧ (∀ x ∈ N, x ∈ N') ∧
      N' = IntermediateField.adjoin (K₀ K t) (N : Set Ω) := by
  classical
  haveI : CharZero (K₀ k t) := charZero_of_injective_algebraMap (algebraMap k (K₀ k t)).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : CharZero (K₀ K t) := charZero_of_injective_algebraMap (algebraMap K (K₀ K t)).injective
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (K₀ k t) F
  set θ : Ω := (α : Ω)
  have hθint : IsIntegral (K₀ k t) θ :=
    (IsIntegral.of_finite (K₀ k t) α).map (IsScalarTower.toAlgHom (K₀ k t) F Ω)
  set p := minpoly (K₀ k t) θ
  have hp0 : p ≠ 0 := minpoly.ne_zero hθint
  set R := p.rootSet Ω
  set N := IntermediateField.adjoin (K₀ k t) R
  set p' := p.map (K₀Map (K := K) t)
  have hp'0 : p' ≠ 0 := Polynomial.map_ne_zero hp0
  set N' := IntermediateField.adjoin (K₀ K t) (p'.rootSet Ω)
  have hR : p'.rootSet Ω = R := rootSet_map_K₀Map p
  haveI hsN : p.IsSplittingField (K₀ k t) N :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI hsN' : p'.IsSplittingField (K₀ K t) N' :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : FiniteDimensional (K₀ k t) N := Polynomial.IsSplittingField.finiteDimensional N p
  haveI : FiniteDimensional (K₀ K t) N' := Polynomial.IsSplittingField.finiteDimensional N' p'
  haveI : Normal (K₀ k t) N := Normal.of_isSplittingField p
  haveI : Normal (K₀ K t) N' := Normal.of_isSplittingField p'
  haveI : Algebra.IsSeparable (K₀ k t) N := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable (K₀ K t) N' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hθR : θ ∈ R := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hp0, minpoly.aeval _ _⟩
  have hFN : F ≤ N := by
    intro x hx
    have h1 : (⟨x, hx⟩ : F) ∈ (K₀ k t)⟮α⟯ := hα ▸ IntermediateField.mem_top
    have h2 : x ∈ ((K₀ k t)⟮α⟯).map F.val := ⟨_, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    exact (IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.subset_adjoin _ _ hθR)) h2
  have hNN' : ∀ x ∈ N, x ∈ N' := by
    let N'k : IntermediateField (K₀ k t) Ω :=
      N'.toSubfield.toIntermediateField fun c => N'.algebraMap_mem (K₀Map (K := K) t c)
    have : N ≤ N'k := by
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      change y ∈ N'
      rw [← hR] at hy
      exact IntermediateField.subset_adjoin _ _ hy
    exact fun x hx => this hx
  refine ⟨N, N', hFN, inferInstance, IsGalois.mk, inferInstance, IsGalois.mk, hNN', ?_⟩
  apply le_antisymm
  · show IntermediateField.adjoin (K₀ K t) (p'.rootSet Ω) ≤ _
    rw [hR]
    exact IntermediateField.adjoin.mono _ _ _ (IntermediateField.subset_adjoin _ _)
  · rw [IntermediateField.adjoin_le_iff]
    exact fun x hx => hNN' x hx

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Ramification indices are invariant under extension of the constant field.** Let
`F₁ ⊆ F₂` be finite extensions of `k(t)` in `Ω` (algebraically closed) and `F₁' ⊆ F₂'` their
composita with `K(t)`. For a maximal ideal `w'` of the coordinate ring of `F₂'`, the prime
`w = w' ∩ coordRing F₂` is either `0`, and then `w'` is unramified over `F₁'`, or maximal, and then
`e(w' | F₁') = e(w | F₁)`. -/
theorem ramificationIdx_bc (htK : Transcendental K t)
    {F₁ F₂ : IntermediateField (K₀ k t) Ω} {F₁' F₂' : IntermediateField (K₀ K t) Ω}
    [FiniteDimensional (K₀ k t) F₂] (h : F₁ ≤ F₂) (h' : F₁' ≤ F₂')
    (h₁ : ∀ x ∈ F₁, x ∈ F₁') (h₂ : ∀ x ∈ F₂, x ∈ F₂')
    (h₁' : F₁' ≤ IntermediateField.adjoin (K₀ K t) (F₁ : Set Ω))
    (h₂' : F₂' ≤ IntermediateField.adjoin (K₀ K t) (F₂ : Set Ω))
    (w' : Ideal (coordRing K t F₂')) [hw' : w'.IsMaximal] :
    (w'.comap (bcMap h₂) = ⊥ →
      (letI := algRing t h'; w'.ramificationIdx (coordRing K t F₁')) = 1) ∧
    (w'.comap (bcMap h₂) ≠ ⊥ → (w'.comap (bcMap h₂)).IsMaximal ∧
      (letI := algRing t h'; w'.ramificationIdx (coordRing K t F₁')) =
        (letI := algRing t h; (w'.comap (bcMap h₂)).ramificationIdx (coordRing k t F₁))) := by
  have htk : Transcendental k t := transcendental_of_bc (K := K) htK
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain ⟨N, N', hF₂N, _, _, _, _, hNN', hN'⟩ := exists_galois_bc htK F₂
  have hF₂'N' : F₂' ≤ N' := by
    rw [hN']
    exact h₂'.trans (IntermediateField.adjoin.mono _ _ _ hF₂N)
  haveI : FiniteDimensional (K₀ K t) F₂' :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hF₂'N').toLinearMap
      (IntermediateField.inclusion hF₂'N').injective
  haveI : Algebra.IsSeparable (K₀ K t) F₂' :=
    Algebra.IsSeparable.of_algHom (F := K₀ K t) (E := F₂') (E' := N')
      (IntermediateField.inclusion hF₂'N')
  haveI : Algebra.IsSeparable (K₀ k t) F₂ :=
    Algebra.IsSeparable.of_algHom (F := K₀ k t) (E := F₂) (E' := N)
      (IntermediateField.inclusion hF₂N)
  haveI := isDedekindDomain_ring t htk F₂
  haveI := isDedekindDomain_ring t htk N
  haveI := isDedekindDomain_ring t htK N'
  -- a prime `u'` of `N'` over `w'`
  obtain ⟨u', hu', hu'w⟩ : ∃ u' : Ideal (coordRing K t N'), u'.IsMaximal ∧
      u'.comap (ringMap t hF₂'N') = w' := by
    letI := algRing t hF₂'N'
    haveI : Algebra.IsIntegral (coordRing K t F₂') (coordRing K t N') := ⟨ringMap_isIntegral t _⟩
    have hker : RingHom.ker (algebraMap (coordRing K t F₂') (coordRing K t N')) ≤ w' := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      rw [show x = 0 from ringMap_injective t hF₂'N' (hx.trans (map_zero _).symm)]
      exact zero_mem _
    exact Ideal.exists_ideal_over_maximal_of_isIntegral w' hker
  set u := u'.comap (bcMap hNN')
  haveI : u.IsPrime := Ideal.comap_isPrime _ _
  have hwu : w'.comap (bcMap h₂) = u.comap (ringMap t hF₂N) := by
    rw [← hu'w]
    ext x
    exact Iff.rfl
  have hu0 : w'.comap (bcMap h₂) = ⊥ ↔ u = ⊥ := by
    constructor
    · intro hw0
      by_contra hne
      letI := algRing t hF₂N
      haveI : Algebra.IsIntegral (coordRing k t F₂) (coordRing k t N) := ⟨ringMap_isIntegral t _⟩
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
        (hwu ▸ hw0)
    · intro hu
      rw [hwu, hu]
      exact Ideal.comap_bot_of_injective _ (ringMap_injective t hF₂N)
  have hmc' := ramificationIdx_mul_card t htK h' hF₂'N' u'
  rw [hu'w] at hmc'
  refine ⟨fun hw0 => ?_, fun hw0 => ?_⟩
  · -- `u' ∩ N = 0`: trivial inertia
    have hI : u'.inertia (N' ≃ₐ[K₀ K t] N') = ⊥ := by
      rw [eq_bot_iff]
      intro σ' hσ'
      exact inertia_eq_bot hNN' (le_of_eq hN') u' (hu0.mp hw0) σ' hσ'
    rw [hI, bot_inf_eq, bot_inf_eq, Subgroup.card_bot, mul_one] at hmc'
    exact hmc'
  · have hune : u ≠ ⊥ := fun h0 => hw0 (hu0.mpr h0)
    haveI hum : u.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hune
    refine ⟨?_, ?_⟩
    · rw [hwu]
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ (ringMap_isIntegral t _) u
    · have hmc := ramificationIdx_mul_card t htk h hF₂N u
      rw [← hwu] at hmc
      have c1 := card_inertia_inf_fixSub hNN' htK (le_of_eq hN') (h.trans hF₂N) h₁ h₁' u' hune
      have c2 := card_inertia_inf_fixSub hNN' htK (le_of_eq hN') hF₂N h₂ h₂' u' hune
      rw [c1, c2] at hmc'
      rw [← hmc] at hmc'
      have hpos : 0 < Nat.card (u.inertia (N ≃ₐ[K₀ k t] N) ⊓ fixSub t N F₂ : Subgroup _) :=
        Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos hmc'

omit [IsAlgClosed Ω] in
set_option linter.unusedSectionVars false in
/-- **Restriction is surjective** when `k` is algebraically closed (`K(t) ∩ N = k(t)`). -/
theorem res_surjective [IsAlgClosed k] (htK : Transcendental K t)
    {N : IntermediateField (K₀ k t) Ω} {N' : IntermediateField (K₀ K t) Ω}
    (hN : ∀ x ∈ N, x ∈ N') [FiniteDimensional (K₀ k t) N] [IsGalois (K₀ k t) N]
    [FiniteDimensional (K₀ K t) N'] [IsGalois (K₀ K t) N'] :
    Function.Surjective (res hN) := by
  rw [← MonoidHom.range_eq_top]
  set H := (res hN).range
  have hfix : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    -- `x` is fixed by `Gal(N' / K(t))`, so `x ∈ K(t)`
    have hx' : (⟨x, hN x x.2⟩ : N') ∈ (⊥ : IntermediateField (K₀ K t) N') := by
      rw [← IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField (K₀ K t) N'),
        IntermediateField.fixingSubgroup_bot, IntermediateField.mem_fixedField_iff]
      intro σ' _
      have := congrArg Subtype.val (hx (res hN σ') ⟨σ', rfl⟩)
      rw [coe_res_apply] at this
      exact Subtype.ext this
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hx'
    have hxK : (x : Ω) ∈ K₀ K t := by
      rw [← congrArg Subtype.val hc]; exact c.2
    have halg : IsAlgebraic (K₀ k t) (x : Ω) :=
      ((IsIntegral.of_finite (K₀ k t) x).map (IsScalarTower.toAlgHom (K₀ k t) N Ω)).isAlgebraic
    have hxk := mem_K₀_of_isAlgebraic htK hxK halg
    exact IntermediateField.mem_bot.mpr ⟨⟨x, hxk⟩, Subtype.ext rfl⟩
  rw [← IntermediateField.fixingSubgroup_fixedField H, hfix, IntermediateField.fixingSubgroup_bot]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Lying over under extension of an algebraically closed constant field**: if `k` is
algebraically closed, every maximal ideal of the coordinate ring of `F` is the trace of a maximal
ideal of the coordinate ring of `F' = K(t) · F`. -/
theorem exists_comap_bc_eq [IsAlgClosed k] (htK : Transcendental K t)
    {F : IntermediateField (K₀ k t) Ω} {F' : IntermediateField (K₀ K t) Ω}
    [FiniteDimensional (K₀ k t) F] (hF : ∀ x ∈ F, x ∈ F')
    (hF' : F' ≤ IntermediateField.adjoin (K₀ K t) (F : Set Ω))
    (w : Ideal (coordRing k t F)) [hw : w.IsMaximal] :
    ∃ w' : Ideal (coordRing K t F'), w'.IsMaximal ∧ w'.comap (bcMap hF) = w := by
  classical
  have htk : Transcendental k t := transcendental_of_bc (K := K) htK
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain ⟨N, N', hFN, _, _, _, _, hNN', hN'⟩ := exists_galois_bc htK F
  have hF'N' : F' ≤ N' := by
    rw [hN']
    exact hF'.trans (IntermediateField.adjoin.mono _ _ _ hFN)
  haveI : Algebra.IsSeparable (K₀ k t) F :=
    Algebra.IsSeparable.of_algHom (F := K₀ k t) (E := F) (E' := N) (IntermediateField.inclusion hFN)
  haveI := isDedekindDomain_ring t htk F
  haveI := isDedekindDomain_ring t htk N
  haveI := isDedekindDomain_ring t htK N'
  -- a prime `u` of `N` over `w`
  obtain ⟨u, hu, huw⟩ : ∃ u : Ideal (coordRing k t N), u.IsMaximal ∧
      u.comap (ringMap t hFN) = w := by
    letI := algRing t hFN
    haveI : Algebra.IsIntegral (coordRing k t F) (coordRing k t N) := ⟨ringMap_isIntegral t _⟩
    have hker : RingHom.ker (algebraMap (coordRing k t F) (coordRing k t N)) ≤ w := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      rw [show x = 0 from ringMap_injective t hFN (hx.trans (map_zero _).symm)]
      exact zero_mem _
    exact Ideal.exists_ideal_over_maximal_of_isIntegral w hker
  -- `p = u ∩ k[t] = (t - c)`
  have hbotN : (⊥ : IntermediateField (K₀ k t) Ω) ≤ N := bot_le
  have hbotN' : (⊥ : IntermediateField (K₀ K t) Ω) ≤ N' := bot_le
  set p := u.comap (ringMap t hbotN)
  haveI : p.IsMaximal := by
    letI := algRing t hbotN
    haveI : Algebra.IsIntegral (coordRing k t (⊥ : IntermediateField (K₀ k t) Ω))
      (coordRing k t N) := ⟨ringMap_isIntegral t _⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal u
  set ek := coordRingBotEquiv (Ω := Ω) htk
  set eK := coordRingBotEquiv (Ω := Ω) htK
  set P : Ideal k[X] := p.comap ek.toRingEquiv.toRingHom
  haveI hPm : P.IsMaximal := Ideal.comap_isMaximal_of_surjective _ ek.surjective
  obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal P).principal
  have hPq : P = Ideal.span {q} := hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    have : P = ⊥ := by rw [hPq, Ideal.span_singleton_eq_bot.mpr rfl]
    exact Ring.ne_bot_of_isMaximal_of_not_isField hPm (Polynomial.not_isField k) this
  have hqu : ¬ IsUnit q := fun h => hPm.ne_top (by rw [hPq, Ideal.span_singleton_eq_top]; exact h)
  obtain ⟨c, hc⟩ :=
    IsAlgClosed.exists_root q (fun h => hqu (Polynomial.isUnit_iff_degree_eq_zero.mpr h))
  have hPc : P = RingHom.ker (Polynomial.evalRingHom c) := by
    refine hPm.eq_of_le (RingHom.ker_ne_top _) ?_
    rw [hPq, Ideal.span_le, Set.singleton_subset_iff]
    exact hc
  -- the maximal ideal `v' = (t - c)` of `K[t]`
  let χ : coordRing K t (⊥ : IntermediateField (K₀ K t) Ω) →+* K :=
    (Polynomial.evalRingHom (algebraMap k K c)).comp eK.symm.toRingEquiv.toRingHom
  have hχ : Function.Surjective χ := fun a => ⟨eK (Polynomial.C a), by simp [χ]⟩
  set v' := RingHom.ker χ
  haveI hv' : v'.IsMaximal := RingHom.ker_isMaximal_of_surjective χ hχ
  have hv'p : v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t))) = p := by
    ext x
    obtain ⟨r, rfl⟩ := ek.surjective x
    rw [Ideal.mem_comap, RingHom.mem_ker, bcMap_coordRingBotEquiv htk htK]
    have h1 : χ (eK (r.map (algebraMap k K))) = algebraMap k K (r.eval c) := by
      change Polynomial.eval (algebraMap k K c) (eK.symm (eK (r.map (algebraMap k K)))) = _
      rw [AlgEquiv.symm_apply_apply, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [h1, map_eq_zero_iff _ (algebraMap k K).injective]
    change _ ↔ r ∈ P
    rw [hPc, RingHom.mem_ker]
    rfl
  -- a prime `u'₁` of `N'` over `v'`
  obtain ⟨u'₁, hu'₁, hu'₁v⟩ : ∃ u'₁ : Ideal (coordRing K t N'), u'₁.IsMaximal ∧
      u'₁.comap (ringMap t hbotN') = v' := by
    letI := algRing t hbotN'
    haveI : Algebra.IsIntegral (coordRing K t (⊥ : IntermediateField (K₀ K t) Ω))
      (coordRing K t N') := ⟨ringMap_isIntegral t _⟩
    have hker : RingHom.ker (algebraMap (coordRing K t (⊥ : IntermediateField (K₀ K t) Ω))
        (coordRing K t N')) ≤ v' := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      rw [show x = 0 from ringMap_injective t hbotN' (hx.trans (map_zero _).symm)]
      exact zero_mem _
    exact Ideal.exists_ideal_over_maximal_of_isIntegral v' hker
  set u₁ := u'₁.comap (bcMap hNN')
  haveI : u₁.IsPrime := Ideal.comap_isPrime _ _
  have hu₁p : u₁.comap (ringMap t hbotN) = p := by
    rw [← hv'p, ← hu'₁v]
    ext x
    exact Iff.rfl
  -- transitivity of `Gal(N / k(t))` on the primes over `p`
  obtain ⟨σ, hσ⟩ : ∃ σ : fixSub t N ⊥, σ • u₁ = u := by
    letI := algRing t hbotN
    haveI := isGaloisGroup_fixSub t hbotN htk
    haveI : u.LiesOver p := ⟨rfl⟩
    haveI : u₁.LiesOver p := ⟨hu₁p.symm⟩
    exact Ideal.exists_smul_eq_of_isGaloisGroup p u₁ u (fixSub t N ⊥)
  obtain ⟨σ', hσ'⟩ := res_surjective htK hNN' (σ : N ≃ₐ[K₀ k t] N)
  let u' : Ideal (coordRing K t N') := σ' • u'₁
  have hu' : u'.IsMaximal := by
    change (σ' • u'₁).IsMaximal
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _ (MulSemiringAction.toRingAut _ _ σ').symm.surjective
  have hu'u : u'.comap (bcMap hNN') = u := by
    rw [← hσ]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.smul_def, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← hσ', ← map_inv,
      ← bcMap_smul]
    exact Iff.rfl
  refine ⟨u'.comap (ringMap t hF'N'),
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ (ringMap_isIntegral t _) u', ?_⟩
  rw [← huw, ← hu'u]
  ext x
  exact Iff.rfl

end Closure

end AffOrbicurve
