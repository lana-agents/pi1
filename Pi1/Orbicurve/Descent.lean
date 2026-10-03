module

public import Pi1.Orbicurve.Lefschetz
public import Mathlib.RingTheory.Polynomial.Subring
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Descent of the data of `CoreStar` to algebraically closed subfields

* `AffOrbicurve.mem_A₀_of_mem_K₀`: `K[t] ∩ k(t) = k[t]`;
* `AffOrbicurve.isIntegral_A₀_of_bc`: for `k ⊆ K` algebraically closed, an element algebraic over
  `k(t)` and integral over `K[t]` is integral over `k[t]`.
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω] {t : Ω}

/-- **`K[t] ∩ k(t) = k[t]`.** -/
lemma mem_A₀_of_mem_K₀ (htK : Transcendental K t) {z : Ω} (hz : z ∈ K₀ k t) (hzK : z ∈ A₀ K t) :
    z ∈ A₀ k t := by
  classical
  obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).mp hz
  obtain ⟨R, hR⟩ : ∃ R : K[X], aeval t R = z := by
    have h : z ∈ (aeval t : K[X] →ₐ[K] Ω).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact hzK
    obtain ⟨R, hR⟩ := h
    exact ⟨R, hR⟩
  by_cases hQ : aeval t Q = 0
  · rw [hQ, div_zero] at hPQ
    rw [hPQ]; exact zero_mem _
  have hQ0 : Q ≠ 0 := fun h => hQ (by rw [h, map_zero])
  -- `Q R = P` in `K[X]`
  have hinj := transcendental_iff_injective.mp htK
  have hrel : Q.map (algebraMap k K) * R = P.map (algebraMap k K) := by
    apply hinj
    rw [map_mul, aeval_map_algebraMap, aeval_map_algebraMap, hR, hPQ]
    field_simp
  -- divide `P` by `Q` in `k[X]`
  set D := P / Q
  set M := P % Q
  have hPM : P = Q * D + M := (EuclideanDomain.div_add_mod P Q).symm
  have hM : M.degree < Q.degree := EuclideanDomain.mod_lt P hQ0
  have h2 : Q.map (algebraMap k K) * (R - D.map (algebraMap k K)) = M.map (algebraMap k K) := by
    rw [mul_sub, hrel, hPM, Polynomial.map_add, Polynomial.map_mul]; ring
  have hRD : R = D.map (algebraMap k K) := by
    by_contra hne
    have hne' : R - D.map (algebraMap k K) ≠ 0 := sub_ne_zero.mpr hne
    have hdeg := congrArg Polynomial.degree h2
    rw [Polynomial.degree_mul, Polynomial.degree_map, Polynomial.degree_map] at hdeg
    have : Q.degree ≤ Q.degree + (R - D.map (algebraMap k K)).degree := by
      have h0 : (0 : WithBot ℕ) ≤ (R - D.map (algebraMap k K)).degree := by
        rw [Polynomial.degree_eq_natDegree hne']; exact WithBot.coe_le_coe.mpr (Nat.zero_le _)
      exact le_add_of_nonneg_right h0
    exact absurd (hdeg ▸ this) (not_le.mpr hM)
  rw [← hR, hRD, aeval_map_algebraMap]
  exact Polynomial.aeval_mem_adjoin_singleton k t

lemma isIntegral_of_roots {R : Subalgebra (A₀ K t) Ω} {p : (K₀ k t)[X]} (hm : p.Monic)
    (hs : (p.map (algebraMap (K₀ k t) Ω)).Splits)
    (hr : ∀ r ∈ p.rootSet Ω, r ∈ R) (i : ℕ) : ((p.coeff i : K₀ k t) : Ω) ∈ R := by
  classical
  set q := p.map (algebraMap (K₀ k t) Ω)
  have hq : q = (q.roots.map (X - C ·)).prod := hs.eq_prod_roots_of_monic (hm.map _)
  have hR : ∀ r ∈ q.roots, r ∈ R := by
    intro r hr'
    apply hr
    rw [Polynomial.mem_rootSet]
    exact ⟨hm.ne_zero, by
      rw [aeval_def, ← eval_map]; exact (Polynomial.mem_roots (hm.map _).ne_zero).mp hr'⟩
  let rootsR : Multiset R := q.roots.attach.map fun r => ⟨r.1, hR r.1 r.2⟩
  let QR : R[X] := (rootsR.map (X - C ·)).prod
  have hQR : QR.map R.val.toRingHom = q := by
    rw [hq, Polynomial.map_multiset_prod, Multiset.map_map]
    simp only [rootsR, Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    congr 1
    conv_rhs => rw [← Multiset.attach_map_val q.roots, Multiset.map_map]
    rfl
  have : ((p.coeff i : K₀ k t) : Ω) = q.coeff i := by rw [Polynomial.coeff_map]; rfl
  rw [this, ← hQR, Polynomial.coeff_map]
  exact (QR.coeff i).2

variable [IsAlgClosed Ω] [CharZero k]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Integrality descends to an algebraically closed subfield of constants.** -/
theorem isIntegral_A₀_of_bc [IsAlgClosed k] (htK : Transcendental K t) {x : Ω}
    (hxa : IsIntegral (K₀ k t) x) (hx : IsIntegral (A₀ K t) x) : IsIntegral (A₀ k t) x := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let F : IntermediateField (K₀ k t) Ω := IntermediateField.adjoin (K₀ k t) {x}
  haveI : FiniteDimensional (K₀ k t) F := IntermediateField.adjoin.finiteDimensional hxa
  obtain ⟨N, N', hFN, _, _, _, _, hNN', -⟩ := exists_galois_bc htK F
  have hxN : x ∈ N := hFN (IntermediateField.mem_adjoin_simple_self _ x)
  set p := minpoly (K₀ k t) x
  have hm : p.Monic := minpoly.monic hxa
  let R : Subalgebra (A₀ K t) Ω := integralClosure (A₀ K t) Ω
  -- the roots of `p` are integral over `K[t]`
  have hroots : ∀ r ∈ p.rootSet Ω, r ∈ R := by
    intro r hr
    rw [Polynomial.mem_rootSet] at hr
    have hsplit : (p.map (algebraMap (K₀ k t) N)).Splits := by
      have := Normal.splits (F := K₀ k t) (K := N) inferInstance ⟨x, hxN⟩
      rwa [IntermediateField.minpoly_eq] at this
    have hroot : ((p.map (algebraMap (K₀ k t) N)).map (algebraMap N Ω)).IsRoot r := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.IsRoot, eval_map,
        ← aeval_def]
      exact hr.2
    obtain ⟨r', hr'⟩ := hsplit.mem_range_of_isRoot (Polynomial.map_ne_zero hr.1) hroot
    have hr'0 : aeval r' p = 0 := by
      apply (algebraMap N Ω).injective
      rw [map_zero, ← aeval_algebraMap_apply, hr']
      exact hr.2
    have hmin : minpoly (K₀ k t) (⟨x, hxN⟩ : N) = minpoly (K₀ k t) r' := by
      have e1 : minpoly (K₀ k t) (⟨x, hxN⟩ : N) = p := IntermediateField.minpoly_eq _
      rw [e1]
      exact minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hxa) hr'0 hm
    obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K₀ k t) (E := N)).mp hmin.symm
    obtain ⟨σ', rfl⟩ := res_surjective htK hNN' τ
    -- `r = σ'(x)`
    have hrσ : r = ((σ' ⟨x, hNN' x hxN⟩ : N') : Ω) := by
      rw [← hr', ← hτ]
      exact (coe_res_apply hNN' σ' ⟨x, hxN⟩).symm
    rw [hrσ]
    -- `σ'` preserves integrality over `K[t]`
    obtain ⟨f, hfm, hf⟩ := hx
    refine ⟨f, hfm, ?_⟩
    have h0 : Polynomial.eval₂ (algebraMap (A₀ K t) N') ⟨x, hNN' x hxN⟩ f = 0 := by
      apply Subtype.val_injective
      have := Polynomial.hom_eval₂ f (algebraMap (A₀ K t) N') N'.val.toRingHom ⟨x, hNN' x hxN⟩
      change N'.val.toRingHom _ = 0
      rw [this]
      exact hf
    have h1 : Polynomial.eval₂ (algebraMap (A₀ K t) N') (σ' ⟨x, hNN' x hxN⟩) f = 0 := by
      have := Polynomial.hom_eval₂ f (algebraMap (A₀ K t) N') σ'.toRingEquiv.toRingHom
        ⟨x, hNN' x hxN⟩
      have hc : σ'.toRingEquiv.toRingHom.comp (algebraMap (A₀ K t) N') =
          algebraMap (A₀ K t) N' := by
        refine RingHom.ext fun a => ?_
        change σ' (algebraMap (K₀ K t) N' (algebraMap (A₀ K t) (K₀ K t) a)) = _
        rw [AlgEquiv.commutes]; rfl
      rw [hc, h0, map_zero] at this
      exact this.symm
    have := Polynomial.hom_eval₂ f (algebraMap (A₀ K t) N') N'.val.toRingHom (σ' ⟨x, hNN' x hxN⟩)
    rw [h1, map_zero] at this
    exact this.symm
  -- the coefficients of `p` lie in `k[t]`
  have hsplitΩ : (p.map (algebraMap (K₀ k t) Ω)).Splits := IsAlgClosed.splits _
  have hcoeff : ∀ i, ((p.coeff i : K₀ k t) : Ω) ∈ A₀ k t := by
    intro i
    have hR := isIntegral_of_roots hm hsplitΩ hroots i
    have hK : ((p.coeff i : K₀ k t) : Ω) ∈ K₀ K t := K₀_le_bc t (p.coeff i).2
    haveI := isPrincipalIdealRing_A₀ htK
    have h1 : IsIntegral (A₀ K t) (⟨_, hK⟩ : K₀ K t) := by
      haveI : IsScalarTower (A₀ K t) (K₀ K t) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact (isIntegral_algebraMap_iff (algebraMap (K₀ K t) Ω).injective).mp hR
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A₀ K t) (K := K₀ K t)).mp h1
    have hA : ((p.coeff i : K₀ k t) : Ω) ∈ A₀ K t := by
      rw [← congrArg Subtype.val ha]; exact a.2
    exact mem_A₀_of_mem_K₀ htK (p.coeff i).2 hA
  -- conclusion
  set q := p.map (algebraMap (K₀ k t) Ω)
  have hqc : (↑q.coeffs : Set Ω) ⊆ (A₀ k t).toSubring := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hz
    rw [Polynomial.coeff_map]
    exact hcoeff i
  let pA : (A₀ k t)[X] := q.toSubring (A₀ k t).toSubring hqc
  refine ⟨pA, (Polynomial.monic_toSubring _ _ _).mpr (hm.map _), ?_⟩
  have h1 : pA.map (algebraMap (A₀ k t) Ω) = q := Polynomial.map_toSubring q (A₀ k t).toSubring hqc
  rw [← Polynomial.eval_map, h1, Polynomial.eval_map, ← aeval_def]
  exact minpoly.aeval _ _

omit [Field K] [Algebra k K] [Algebra K Ω] [IsScalarTower k K Ω] [IsAlgClosed Ω] [CharZero k] in
/-- **Exchange**: if `s` is transcendental over `k` and algebraic over `k[t]`, then `t` is
algebraic over `k[s]`. -/
lemma isAlgebraic_exchange {s : Ω} (hs : Transcendental k s) (hst : IsAlgebraic (A₀ k t) s) :
    IsAlgebraic (A₀ k s) t := by
  by_contra h
  have h' : Transcendental (Algebra.adjoin k (Set.range fun _ : Unit => s)) t := by
    rw [Set.range_const]; exact h
  have hx : AlgebraicIndependent k (fun _ : Unit => s) :=
    (algebraicIndependent_unique_type_iff).mpr hs
  have hy := (hx.option_iff_transcendental t).mpr h'
  let e : Option Unit → Option Unit := fun o => o.elim (some ()) (fun _ => none)
  have he : Function.Injective e := by
    intro a b hab
    rcases a with _ | ⟨⟨⟩⟩ <;> rcases b with _ | ⟨⟨⟩⟩ <;> simp_all [e]
  have hz := hy.comp e he
  have hz' : AlgebraicIndependent k (fun o : Option Unit => o.elim s (fun _ : Unit => t)) := by
    convert hz using 1
    funext o
    rcases o with _ | ⟨⟨⟩⟩ <;> rfl
  have ht : AlgebraicIndependent k (fun _ : Unit => t) := by
    have := hz'.comp (fun u : Unit => some u) (Option.some_injective _)
    exact this
  have := (ht.option_iff_transcendental s).mp hz'
  rw [Set.range_const] at this
  exact this hst

end AffOrbicurve
