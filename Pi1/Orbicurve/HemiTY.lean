/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Orbicurve.BaseChange
public import Pi1.Orbicurve.SubfieldRamified

/-!
# Double covers of the `t`-line and their quotient orbicurves

For `t ∈ Ω` transcendental over `F` and `y ∈ Ω` a root of a quadratic `Y² + bY - c` with
`b, c ∈ F(t)`, `fnTY F t y = F(t)(y)` is a normal extension of `F(t)` of degree `≤ 2`
(`normal_fnTY`), and `hemiTY F t y` is the `t`-line with stabilizer orders the ramification
indices of `F(t)(y) / F(t)` (`multTY`); these are the same at all primes over a given prime
(`multTY_eq`). For `y² + (a₁t + a₃)y = t³ + a₂t² + a₄t + a₆` this is the punctured hemi-elliptic
orbicurve (`Pi1.Orbicurve.EllipticSubfield`). These objects only depend on the elements `t, y`
of `Ω`, which makes them convenient for base change (`multTY_bc`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable (F : Type u) {Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] (t y : Ω)

/-- `F(t)(y) ⊆ Ω`. -/
noncomputable abbrev fnTY : IntermediateField (K₀ F t) Ω := IntermediateField.adjoin (K₀ F t) {y}

variable {F t y}

lemma isIntegral_of_quadratic {b c : Ω} (hb : b ∈ K₀ F t) (hc : c ∈ K₀ F t)
    (hy : y ^ 2 + b * y = c) : IsIntegral (K₀ F t) y := by
  refine ⟨X ^ 2 + (C (⟨b, hb⟩ : K₀ F t) * X - C (⟨c, hc⟩ : K₀ F t)), monic_X_pow_add ?_, ?_⟩
  · refine (degree_sub_le _ _).trans_lt ?_
    refine max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num)) ?_
    exact degree_C_le.trans_lt (by norm_num)
  · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X]
    change y ^ 2 + (b * y - c) = 0
    linear_combination hy

lemma finiteDimensional_fnTY {b c : Ω} (hb : b ∈ K₀ F t) (hc : c ∈ K₀ F t)
    (hy : y ^ 2 + b * y = c) : FiniteDimensional (K₀ F t) (fnTY F t y) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_of_quadratic hb hc hy)

lemma isSeparable_fnTY [CharZero F] [FiniteDimensional (K₀ F t) (fnTY F t y)] :
    Algebra.IsSeparable (K₀ F t) (fnTY F t y) := by
  haveI : CharZero (K₀ F t) :=
    charZero_of_injective_algebraMap (algebraMap F (K₀ F t)).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- `F(t)(y) / F(t)` is normal (the splitting field of `Y² + bY - c`). -/
lemma normal_fnTY [IsAlgClosed Ω] {b c : Ω} (hb : b ∈ K₀ F t) (hc : c ∈ K₀ F t)
    (hy : y ^ 2 + b * y = c) : Normal (K₀ F t) (fnTY F t y) := by
  let bb : K₀ F t := ⟨b, hb⟩
  let cc : K₀ F t := ⟨c, hc⟩
  let Q : (K₀ F t)[X] := X ^ 2 + (C bb * X - C cc)
  have hQ0 : Q ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_zero] at this
    have hd : Q.natDegree = 2 := by
      apply Polynomial.natDegree_eq_of_degree_eq_some
      rw [Polynomial.degree_add_eq_left_of_degree_lt]
      · simp
      · rw [Polynomial.degree_X_pow]
        refine (degree_sub_le _ _).trans_lt ?_
        refine max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num)) ?_
        exact degree_C_le.trans_lt (by norm_num)
    omega
  have hev : ∀ z : Ω, aeval z Q = z ^ 2 + b * z - c := by
    intro z
    simp only [Q, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
    change _ = z ^ 2 + (algebraMap (K₀ F t) Ω bb) * z - (algebraMap (K₀ F t) Ω cc)
    ring
  have hyQ : aeval y Q = 0 := by rw [hev]; linear_combination hy
  have hymem : y ∈ fnTY F t y := IntermediateField.subset_adjoin _ _ rfl
  have hroots : Q.rootSet Ω ⊆ fnTY F t y := by
    intro z hz
    rw [Polynomial.mem_rootSet, hev] at hz
    obtain ⟨-, hz⟩ := hz
    have hz' : (z - y) * (z + y + b) = 0 := by linear_combination hz - hy
    have hbmem : b ∈ fnTY F t y := (fnTY F t y).algebraMap_mem bb
    rcases mul_eq_zero.mp hz' with h | h
    · rw [sub_eq_zero.mp h]; exact hymem
    · have : z = -y - b := by linear_combination h
      rw [this]
      exact sub_mem (neg_mem hymem) hbmem
  have heq : IntermediateField.adjoin (K₀ F t) (Q.rootSet Ω) = fnTY F t y := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]; exact hroots
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      apply IntermediateField.subset_adjoin
      rw [Polynomial.mem_rootSet]
      exact ⟨hQ0, hyQ⟩
  haveI hs := IntermediateField.adjoin_rootSet_isSplittingField (K := K₀ F t) (L := Ω) (p := Q)
    (IsAlgClosed.splits _)
  rw [heq] at hs
  exact Normal.of_isSplittingField Q

variable (F t y)

/-- **The stabilizer orders**: the ramification indices of `F(t)(y) / F(t)`. -/
noncomputable def multTY (v : Ideal (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω))) : ℕ :=
  letI := algRing t (bot_le : (⊥ : IntermediateField (K₀ F t) Ω) ≤ fnTY F t y)
  v.ramificationIdxIn (coordRing F t (fnTY F t y))

variable [CharZero F] [FiniteDimensional (K₀ F t) (fnTY F t y)]
  [Algebra.IsSeparable (K₀ F t) (fnTY F t y)] (ht : Transcendental F t)

omit [CharZero F] in
include ht in
set_option synthInstance.maxHeartbeats 400000 in
lemma multTY_pos (v : Ideal (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω)))
    (hv : v.IsMaximal) : 0 < multTY F t y v := by
  have hle : (⊥ : IntermediateField (K₀ F t) Ω) ≤ fnTY F t y := bot_le
  letI iR := algRing t hle
  letI : SMul (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω))
    (coordRing F t (fnTY F t y)) := iR.toSMul
  letI : Module (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω))
    (coordRing F t (fnTY F t y)) := iR.toModule
  haveI := module_finite_ringMap t ht hle
  haveI : Algebra.IsIntegral (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω))
    (coordRing F t (fnTY F t y)) := ⟨ringMap_isIntegral _ _⟩
  haveI : FaithfulSMul (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω))
      (coordRing F t (fnTY F t y)) := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact ringMap_injective _ _
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := coordRing F t (fnTY F t y)) v
  have hex : ∃ P : Ideal (coordRing F t (fnTY F t y)), P.IsPrime ∧ P.LiesOver v :=
    ⟨P, hP.isPrime, hPl⟩
  unfold multTY
  rw [Ideal.ramificationIdxIn, dif_pos hex]
  have := hex.choose_spec.1
  exact Ideal.ramificationIdx_pos _ _

omit [Algebra.IsSeparable (K₀ F t) (fnTY F t y)] in
include ht in
lemma multTY_finite :
    {v : Ideal (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω)) |
      v.IsMaximal ∧ multTY F t y v ≠ 1}.Finite :=
  finite_ramified t ht (bot_le : (⊥ : IntermediateField (K₀ F t) Ω) ≤ fnTY F t y)

/-- **The quotient orbicurve**: the `t`-line with stabilizer orders the ramification indices of
`F(t)(y) / F(t)`. -/
noncomputable def hemiTY : AffOrbicurve F :=
  ofSubfield t ht ⊥ (multTY F t y) (multTY_pos F t y ht) (multTY_finite F t y ht)

variable [IsAlgClosed Ω] [Normal (K₀ F t) (fnTY F t y)]

omit [Algebra.IsSeparable (K₀ F t) (fnTY F t y)] in
include ht in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- All primes over a given prime of `F[t]` have the same ramification index (`F(t)(y) / F(t)`
is Galois). -/
lemma multTY_eq (w : Ideal (coordRing F t (fnTY F t y))) [hw : w.IsMaximal] :
    (letI := algRing t (bot_le : (⊥ : IntermediateField (K₀ F t) Ω) ≤ fnTY F t y);
      w.ramificationIdx (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω))) =
      multTY F t y (w.comap (ringMap t (bot_le : (⊥ : IntermediateField (K₀ F t) Ω) ≤
        fnTY F t y))) := by
  have hle : (⊥ : IntermediateField (K₀ F t) Ω) ≤ fnTY F t y := bot_le
  set v := w.comap (ringMap t hle)
  letI iR := algRing t hle
  haveI : Algebra.IsIntegral (coordRing F t (⊥ : IntermediateField (K₀ F t) Ω))
    (coordRing F t (fnTY F t y)) := ⟨ringMap_isIntegral _ _⟩
  haveI hv : v.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w
  have hex : ∃ P : Ideal (coordRing F t (fnTY F t y)), P.IsPrime ∧ P.LiesOver v :=
    ⟨w, hw.isPrime, ⟨rfl⟩⟩
  unfold multTY
  rw [Ideal.ramificationIdxIn, dif_pos hex]
  obtain ⟨hP, hPl⟩ := hex.choose_spec
  haveI : hex.choose.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal hex.choose v
  obtain ⟨N, -, hAN, _, _, -, -, -, -⟩ := exists_galois_bc (K := F) (fnTY F t y)
  refine ramificationIdx_eq_of_normal t ht hle hAN ?_ w hex.choose hPl.over
  intro σ hσ τ hτ x hx
  have h1 : ((σ⁻¹ x : N) : Ω) ∈ fnTY F t y := mem_of_aut (K := F) (σ⁻¹) x hx
  have h2 : τ (σ⁻¹ x) = σ⁻¹ x := hτ _ h1
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h2]
  exact σ.apply_symm_apply x

/-- **The quotient map** `fnTY → hemiTY`. -/
noncomputable def homTY :
    Hom (ofSubfieldScheme t ht (fnTY F t y)) (hemiTY F t y ht) :=
  homOfLE ht (bot_le : (⊥ : IntermediateField (K₀ F t) Ω) ≤ fnTY F t y) (fun w hw => by
    rw [mul_one]
    exact multTY_eq F t y ht w)

section BC

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω] [CharZero k] {t : Ω} (y : Ω) (htK : Transcendental K t)
  [FiniteDimensional (K₀ k t) (fnTY k t y)] [Algebra.IsSeparable (K₀ k t) (fnTY k t y)]
  [Normal (K₀ k t) (fnTY k t y)]
  [FiniteDimensional (K₀ K t) (fnTY K t y)] [Algebra.IsSeparable (K₀ K t) (fnTY K t y)]
  [Normal (K₀ K t) (fnTY K t y)]

omit [IsAlgClosed Ω] [CharZero k] [FiniteDimensional (K₀ k t) (fnTY k t y)]
  [Algebra.IsSeparable (K₀ k t) (fnTY k t y)] [Normal (K₀ k t) (fnTY k t y)]
  [FiniteDimensional (K₀ K t) (fnTY K t y)] [Algebra.IsSeparable (K₀ K t) (fnTY K t y)]
  [Normal (K₀ K t) (fnTY K t y)] in
lemma fnTY_mem_bc : ∀ x ∈ fnTY k t y, x ∈ fnTY K t y := by
  intro x hx
  obtain ⟨r, q, hrq⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).mp hx
  refine (IntermediateField.mem_adjoin_simple_iff _ _).mpr
    ⟨r.map (K₀Map t), q.map (K₀Map t), ?_⟩
  rw [hrq, aeval_def, aeval_def, aeval_def, aeval_def, eval₂_map, eval₂_map]
  rfl

omit [Algebra.IsSeparable (K₀ k t) (fnTY k t y)] [Algebra.IsSeparable (K₀ K t) (fnTY K t y)] in
include htK in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The stabilizer orders of the quotient orbicurve under base change.** -/
lemma multTY_bc (v' : Ideal (coordRing K t (⊥ : IntermediateField (K₀ K t) Ω)))
    [hv' : v'.IsMaximal] :
    (v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t))) = ⊥ → multTY K t y v' = 1) ∧
    (v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t))) ≠ ⊥ →
      multTY K t y v' = multTY k t y (v'.comap (bcMap bot_mem_bc))) := by
  have htk : Transcendental k t := transcendental_of_bc (K := K) htK
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have hle' : (⊥ : IntermediateField (K₀ K t) Ω) ≤ fnTY K t y := bot_le
  have hle : (⊥ : IntermediateField (K₀ k t) Ω) ≤ fnTY k t y := bot_le
  obtain ⟨u', hu', hu'v⟩ : ∃ u' : Ideal (coordRing K t (fnTY K t y)), u'.IsMaximal ∧
      u'.comap (ringMap t hle') = v' := by
    letI := algRing t hle'
    haveI : Algebra.IsIntegral (coordRing K t (⊥ : IntermediateField (K₀ K t) Ω))
      (coordRing K t (fnTY K t y)) := ⟨ringMap_isIntegral t _⟩
    have hker : RingHom.ker (algebraMap (coordRing K t (⊥ : IntermediateField (K₀ K t) Ω))
        (coordRing K t (fnTY K t y))) ≤ v' := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      rw [show x = 0 from ringMap_injective t hle' (hx.trans (map_zero _).symm)]
      exact zero_mem _
    exact Ideal.exists_ideal_over_maximal_of_isIntegral v' hker
  have hmK := multTY_eq K t y htK u'
  rw [hu'v] at hmK
  have h₂ : ∀ x ∈ fnTY k t y, x ∈ fnTY K t y := fnTY_mem_bc y
  have h₁' : (⊥ : IntermediateField (K₀ K t) Ω) ≤
      IntermediateField.adjoin (K₀ K t) ((⊥ : IntermediateField (K₀ k t) Ω) : Set Ω) := bot_le
  have h₂' : fnTY K t y ≤ IntermediateField.adjoin (K₀ K t) (fnTY k t y : Set Ω) := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin _ _ (IntermediateField.subset_adjoin _ _ rfl)
  obtain ⟨hbot, hne⟩ := ramificationIdx_bc htK hle hle' bot_mem_bc h₂ h₁' h₂' u'
  set u := u'.comap (bcMap h₂)
  have hv : v'.comap (bcMap (bot_mem_bc (k := k) (K := K) (t := t))) = u.comap (ringMap t hle) := by
    rw [← hu'v]; ext x; exact Iff.rfl
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have hu0 : u = ⊥ := by
      by_contra hne'
      letI := algRing t hle
      haveI : Algebra.IsIntegral (coordRing k t (⊥ : IntermediateField (K₀ k t) Ω))
        (coordRing k t (fnTY k t y)) := ⟨ringMap_isIntegral t _⟩
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
      exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
        (hv ▸ h0)
    rw [← hmK]
    exact hbot hu0
  · have hu0 : u ≠ ⊥ := by
      intro hu0
      apply h0
      rw [hv, hu0]
      exact Ideal.comap_bot_of_injective _ (ringMap_injective t hle)
    obtain ⟨hum, he⟩ := hne hu0
    rw [← hmK, he, hv]
    exact multTY_eq k t y htk u

end BC

end AffOrbicurve
