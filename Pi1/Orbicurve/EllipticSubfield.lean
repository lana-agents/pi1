module

public import Pi1.Orbicurve.BaseChange
public import Pi1.Orbicurve.Elliptic
public import Pi1.Orbicurve.SubfieldRamified

/-!
# Once-punctured elliptic curves as subfield orbicurves

Let `E / k` be an elliptic curve and `j : k(E) → Ω` an embedding of its function field into a
field `Ω` over `k`, `t = j(x)`, `y_Ω = j(y)`. The function field `k(E)` becomes the subfield
`fnFieldE j = k(t)(y_Ω)` of `Ω` and

* `AffOrbicurve.isoPuncturedE`: `E ∖ {0}` (`AffOrbicurve.punctured E`) is the normalization of
  the `t`-line in `fnFieldE j`;
* `AffOrbicurve.isoHemiE`: `(E ∖ {0}) / {±1}` (`AffOrbicurve.hemi E`) is the `t`-line with
  stabilizer orders the ramification indices of `fnFieldE j` over `k(t)` (`hemiE j`);
* `AffOrbicurve.homE`: the quotient map `E ∖ {0} → (E ∖ {0}) / {±1}`.
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial WeierstrassCurve

namespace AffOrbicurve

variable {k : Type u} [Field k] (E : WeierstrassCurve k)

/-- The class of `x` in the function field `k(E)`. -/
noncomputable def ellX : E.toAffine.FunctionField :=
  algebraMap E.toAffine.CoordinateRing _ (Affine.CoordinateRing.mk E.toAffine (C X))

/-- The class of `y` in the function field `k(E)`. -/
noncomputable def ellY : E.toAffine.FunctionField :=
  algebraMap E.toAffine.CoordinateRing _ (Affine.CoordinateRing.mk E.toAffine X)

lemma ellY_sq : ellY E ^ 2 + (algebraMap k _ E.a₁ * ellX E + algebraMap k _ E.a₃) * ellY E =
    ellX E ^ 3 + algebraMap k _ E.a₂ * ellX E ^ 2 + algebraMap k _ E.a₄ * ellX E +
      algebraMap k _ E.a₆ := by
  have h : Affine.CoordinateRing.mk E.toAffine (X ^ 2 + C (C E.a₁ * X + C E.a₃) * X -
      C (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) = 0 := AdjoinRoot.mk_self
  have hC : ∀ a : k, Affine.CoordinateRing.mk E.toAffine (C (C a)) =
      algebraMap k E.toAffine.CoordinateRing a := fun _ => rfl
  simp only [map_add, map_sub, map_mul, map_pow, hC] at h
  have := congrArg (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField) h
  simp only [map_add, map_sub, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply] at this
  simp only [ellX, ellY]
  linear_combination this

variable {E} {Ω : Type u} [Field Ω] [Algebra k Ω] (j : E.toAffine.FunctionField →ₐ[k] Ω)

/-- `t = j(x)`. -/
noncomputable def tE : Ω := j (ellX E)

/-- `j(y)`. -/
noncomputable def yE : Ω := j (ellY E)

lemma j_algebraMap_poly (p : k[X]) :
    j (algebraMap k[X] E.toAffine.FunctionField p) = aeval (tE j) p := by
  have h : (j.comp (IsScalarTower.toAlgHom k k[X] E.toAffine.FunctionField)) = aeval (tE j) := by
    apply Polynomial.algHom_ext
    rw [aeval_X]
    change j (algebraMap k[X] E.toAffine.FunctionField X) = j (ellX E)
    rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing E.toAffine.FunctionField]
    rfl
  exact congrArg (fun φ : k[X] →ₐ[k] Ω => φ p) h

lemma transcendental_tE : Transcendental k (tE j) := by
  rintro ⟨p, hp, h⟩
  have hx : aeval (ellX E) p = algebraMap k[X] E.toAffine.FunctionField p := by
    have hX : algebraMap k[X] E.toAffine.FunctionField Polynomial.X = ellX E := by
      rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing]
      rfl
    rw [← hX, aeval_algebraMap_apply, aeval_X_left_apply]
  have h' : j (algebraMap k[X] E.toAffine.FunctionField p) = 0 := by
    rw [← hx, ← Polynomial.aeval_algHom_apply]
    exact h
  have hinj : Function.Injective (algebraMap k[X] E.toAffine.CoordinateRing) := by
    intro p q h
    have h' : (p - q) • (1 : E.toAffine.CoordinateRing) + (0 : k[X]) •
        Affine.CoordinateRing.mk E.toAffine Polynomial.X = 0 := by
      rw [zero_smul, add_zero, sub_smul, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (Affine.CoordinateRing.smul_basis_eq_zero h').1
  have h'' := j.injective (h'.trans (map_zero _).symm)
  rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing] at h''
  refine hp (hinj ?_)
  rw [map_zero]
  exact IsFractionRing.injective E.toAffine.CoordinateRing E.toAffine.FunctionField
    (h''.trans (map_zero _).symm)

/-- **The function field `k(E)` in `Ω`**: `k(t)(y_Ω)`. -/
noncomputable def fnFieldE : IntermediateField (K₀ k (tE j)) Ω :=
  IntermediateField.adjoin (K₀ k (tE j)) {yE j}

lemma tE_mem_K₀ : tE j ∈ K₀ k (tE j) := IntermediateField.mem_adjoin_simple_self k (tE j)

lemma tE_mem_fnFieldE : tE j ∈ fnFieldE j := (fnFieldE j).algebraMap_mem ⟨tE j, tE_mem_K₀ j⟩

lemma yE_mem_fnFieldE : yE j ∈ fnFieldE j := IntermediateField.subset_adjoin _ _ rfl

lemma algebraMap_mem_fnFieldE (c : k) : algebraMap k Ω c ∈ fnFieldE j :=
  (fnFieldE j).algebraMap_mem ⟨_, (K₀ k (tE j)).algebraMap_mem c⟩

lemma coordRing_mem_fnFieldE (a : E.toAffine.CoordinateRing) :
    j (algebraMap _ E.toAffine.FunctionField a) ∈ fnFieldE j := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  induction p using Polynomial.induction_on with
  | C q =>
    induction q using Polynomial.induction_on with
    | C c =>
      have : j (algebraMap _ E.toAffine.FunctionField
          (AdjoinRoot.mk E.toAffine.polynomial (C (C c)))) = algebraMap k Ω c := by
        change j (algebraMap _ _ (algebraMap k E.toAffine.CoordinateRing c)) = _
        rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
      rw [this]; exact algebraMap_mem_fnFieldE j c
    | add q r hq hr => simpa only [C_add, map_add] using add_mem hq hr
    | monomial n c hc =>
      rw [pow_succ, ← mul_assoc, C_mul, map_mul, map_mul, map_mul]
      exact mul_mem hc (tE_mem_fnFieldE j)
  | add p q hp hq => simpa only [map_add] using add_mem hp hq
  | monomial n q hq =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, map_mul]
    exact mul_mem hq (yE_mem_fnFieldE j)

lemma j_mem_fnFieldE (f : E.toAffine.FunctionField) : j f ∈ fnFieldE j := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := E.toAffine.CoordinateRing) f
  rw [map_div₀]
  exact div_mem (coordRing_mem_fnFieldE j a) (coordRing_mem_fnFieldE j b)

lemma exists_of_mem_fnFieldE {z : Ω} (hz : z ∈ fnFieldE j) : ∃ f, j f = z := by
  let S : IntermediateField (K₀ k (tE j)) Ω :=
    j.fieldRange.toSubfield.toIntermediateField (fun x => by
      have : K₀ k (tE j) ≤ j.fieldRange := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact ⟨ellX E, rfl⟩
      exact this x.2)
  have : fnFieldE j ≤ S := by
    rw [fnFieldE, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨ellY E, rfl⟩
  exact this hz

lemma isIntegral_yE : IsIntegral (K₀ k (tE j)) (yE j) := by
  have h' := congrArg j (ellY_sq E)
  simp only [map_add, map_mul, map_pow, AlgHom.commutes] at h'
  let xx : K₀ k (tE j) := ⟨tE j, tE_mem_K₀ j⟩
  let b : K₀ k (tE j) := algebraMap k _ E.a₁ * xx + algebraMap k _ E.a₃
  let c : K₀ k (tE j) := xx ^ 3 + algebraMap k _ E.a₂ * xx ^ 2 +
    algebraMap k _ E.a₄ * xx + algebraMap k _ E.a₆
  refine ⟨X ^ 2 + (C b * X - C c), monic_X_pow_add ?_, ?_⟩
  · refine (degree_sub_le _ _).trans_lt ?_
    refine max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num)) ?_
    exact degree_C_le.trans_lt (by norm_num)
  · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, b, c, xx]
    change j (ellY E) ^ 2 + ((algebraMap k Ω E.a₁ * j (ellX E) + algebraMap k Ω E.a₃) *
      j (ellY E) - (j (ellX E) ^ 3 + algebraMap k Ω E.a₂ * j (ellX E) ^ 2 +
      algebraMap k Ω E.a₄ * j (ellX E) + algebraMap k Ω E.a₆)) = 0
    linear_combination h'

instance finiteDimensional_fnFieldE : FiniteDimensional (K₀ k (tE j)) (fnFieldE j) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_yE j)

instance isSeparable_fnFieldE [CharZero k] : Algebra.IsSeparable (K₀ k (tE j)) (fnFieldE j) := by
  haveI : CharZero (K₀ k (tE j)) :=
    charZero_of_injective_algebraMap (algebraMap k (K₀ k (tE j))).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- `k(E) ≅ fnFieldE j`. -/
noncomputable def funEquiv : E.toAffine.FunctionField ≃+* fnFieldE j :=
  RingEquiv.ofBijective (j.toRingHom.codRestrict (fnFieldE j).toSubfield (j_mem_fnFieldE j))
    ⟨fun a b h => j.injective (congrArg Subtype.val h), fun z => by
      obtain ⟨f, hf⟩ := exists_of_mem_fnFieldE j z.2
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp] lemma coe_funEquiv (f : E.toAffine.FunctionField) :
    ((funEquiv j f : fnFieldE j) : Ω) = j f := rfl

variable [CharZero k] [E.IsElliptic]

/-- The coordinate rings of `E ∖ {0}`: `puncturedRing E ≅ coordRing (fnFieldE j)`. -/
noncomputable def puncturedEquiv : puncturedRing E ≃+* coordRing k (tE j) (fnFieldE j) :=
  integralClosureEquiv (Polynomial.algEquivOfTranscendental k (tE j) (transcendental_tE j)).toRingEquiv
    (funEquiv j) (fun p => by
      apply Subtype.ext
      rw [coe_funEquiv, j_algebraMap_poly]
      exact (coe_algEquivOfTranscendental (transcendental_tE j) p).symm)

@[simp] lemma coe_puncturedEquiv (a : puncturedRing E) :
    (((puncturedEquiv j a : coordRing k (tE j) (fnFieldE j)) : fnFieldE j) : Ω) =
      j (a : E.toAffine.FunctionField) := rfl

/-- **`E ∖ {0}` as a subfield orbicurve.** -/
noncomputable def isoPuncturedE :
    Iso (ofSubfieldScheme (tE j) (transcendental_tE j) (fnFieldE j)) (punctured E) :=
  Iso.ofAlgEquiv
    (AlgEquiv.ofRingEquiv (f := (puncturedEquiv j).symm) fun c => by
      refine ((puncturedEquiv j).symm_apply_eq).mpr ?_
      apply Subtype.ext; apply Subtype.ext
      rw [coe_puncturedEquiv]
      change algebraMap k Ω c = j (algebraMap k E.toAffine.FunctionField c)
      rw [AlgHom.commutes])
    (fun _ _ => rfl)

variable [IsAlgClosed Ω]

/-- `k(E) / k(t)` is normal (a quadratic extension, the splitting field of the Weierstrass
equation in `y`). -/
instance normal_fnFieldE : Normal (K₀ k (tE j)) (fnFieldE j) := by
  set t := tE j
  let xx : K₀ k t := ⟨t, tE_mem_K₀ j⟩
  let b : K₀ k t := algebraMap k _ E.a₁ * xx + algebraMap k _ E.a₃
  let c : K₀ k t := xx ^ 3 + algebraMap k _ E.a₂ * xx ^ 2 +
    algebraMap k _ E.a₄ * xx + algebraMap k _ E.a₆
  let Q : (K₀ k t)[X] := X ^ 2 + (C b * X - C c)
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
  have hy : aeval (yE j) Q = 0 := by
    have h' := congrArg j (ellY_sq E)
    simp only [map_add, map_mul, map_pow, AlgHom.commutes] at h'
    simp only [Q, b, c, xx, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
    change j (ellY E) ^ 2 + ((algebraMap k Ω E.a₁ * j (ellX E) + algebraMap k Ω E.a₃) *
      j (ellY E) - (j (ellX E) ^ 3 + algebraMap k Ω E.a₂ * j (ellX E) ^ 2 +
      algebraMap k Ω E.a₄ * j (ellX E) + algebraMap k Ω E.a₆)) = 0
    linear_combination h'
  have hroots : Q.rootSet Ω ⊆ fnFieldE j := by
    intro z hz
    rw [Polynomial.mem_rootSet] at hz
    obtain ⟨-, hz⟩ := hz
    have hz' : (z - yE j) * (z + yE j + (b : Ω)) = 0 := by
      have e1 : aeval z Q = z ^ 2 + (b : Ω) * z - (c : Ω) := by
        simp only [Q, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
        change _ = z ^ 2 + (algebraMap (K₀ k t) Ω b) * z - (algebraMap (K₀ k t) Ω c) ; ring
      have e2 : aeval (yE j) Q = yE j ^ 2 + (b : Ω) * yE j - (c : Ω) := by
        simp only [Q, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
        change _ = yE j ^ 2 + (algebraMap (K₀ k t) Ω b) * yE j - (algebraMap (K₀ k t) Ω c)
        ring
      rw [e1] at hz; rw [e2] at hy
      linear_combination hz - hy
    have hbmem : (b : Ω) ∈ fnFieldE j := (fnFieldE j).algebraMap_mem b
    rcases mul_eq_zero.mp hz' with h | h
    · rw [sub_eq_zero.mp h]; exact yE_mem_fnFieldE j
    · have : z = -(yE j) - (b : Ω) := by linear_combination h
      rw [this]
      exact sub_mem (neg_mem (yE_mem_fnFieldE j)) hbmem
  have heq : IntermediateField.adjoin (K₀ k t) (Q.rootSet Ω) = fnFieldE j := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]; exact hroots
    · rw [fnFieldE, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      apply IntermediateField.subset_adjoin
      rw [Polynomial.mem_rootSet]
      exact ⟨hQ0, hy⟩
  haveI hs := IntermediateField.adjoin_rootSet_isSplittingField (K := K₀ k t) (L := Ω) (p := Q)
    (IsAlgClosed.splits _)
  rw [heq] at hs
  exact Normal.of_isSplittingField Q

omit [IsAlgClosed Ω] in
lemma bot_le_fnFieldE : (⊥ : IntermediateField (K₀ k (tE j)) Ω) ≤ fnFieldE j := bot_le

/-- **The stabilizer orders of `(E ∖ {0}) / {±1}`**: the ramification indices of `k(E) / k(t)`. -/
noncomputable def multE (v : Ideal (coordRing k (tE j) (⊥ : IntermediateField (K₀ k (tE j)) Ω))) :
    ℕ :=
  letI := algRing (tE j) (bot_le_fnFieldE j)
  v.ramificationIdxIn (coordRing k (tE j) (fnFieldE j))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- All primes over a given prime of `k[t]` have the same ramification index (`k(E) / k(t)` is
Galois). -/
lemma multE_eq (w : Ideal (coordRing k (tE j) (fnFieldE j))) [hw : w.IsMaximal] :
    (letI := algRing (tE j) (bot_le_fnFieldE j);
      w.ramificationIdx (coordRing k (tE j) (⊥ : IntermediateField (K₀ k (tE j)) Ω))) =
      multE j (w.comap (ringMap (tE j) (bot_le_fnFieldE j))) := by
  have ht := transcendental_tE j
  set v := w.comap (ringMap (tE j) (bot_le_fnFieldE j))
  letI iR := algRing (tE j) (bot_le_fnFieldE j)
  haveI : Algebra.IsIntegral (coordRing k (tE j) (⊥ : IntermediateField (K₀ k (tE j)) Ω))
    (coordRing k (tE j) (fnFieldE j)) := ⟨ringMap_isIntegral _ _⟩
  haveI hv : v.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w
  have hex : ∃ P : Ideal (coordRing k (tE j) (fnFieldE j)), P.IsPrime ∧ P.LiesOver v :=
    ⟨w, hw.isPrime, ⟨rfl⟩⟩
  unfold multE
  rw [Ideal.ramificationIdxIn, dif_pos hex]
  obtain ⟨hP, hPl⟩ := hex.choose_spec
  haveI : hex.choose.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal hex.choose v
  obtain ⟨N, -, hAN, _, _, -, -, -, -⟩ := exists_galois_bc (K := k) ht (fnFieldE j)
  refine ramificationIdx_eq_of_normal (tE j) ht (bot_le_fnFieldE j) hAN ?_ w hex.choose hPl.over
  intro σ hσ τ hτ x hx
  have h1 : ((σ⁻¹ x : N) : Ω) ∈ fnFieldE j := mem_of_aut (K := k) (σ⁻¹) x hx
  have h2 : τ (σ⁻¹ x) = σ⁻¹ x := hτ _ h1
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h2]
  exact σ.apply_symm_apply x

set_option synthInstance.maxHeartbeats 400000 in
lemma multE_pos (v : Ideal (coordRing k (tE j) (⊥ : IntermediateField (K₀ k (tE j)) Ω)))
    (hv : v.IsMaximal) : 0 < multE j v := by
  have ht := transcendental_tE j
  letI iR := algRing (tE j) (bot_le_fnFieldE j)
  letI : SMul (coordRing k (tE j) (⊥ : IntermediateField (K₀ k (tE j)) Ω))
    (coordRing k (tE j) (fnFieldE j)) := iR.toSMul
  letI : Module (coordRing k (tE j) (⊥ : IntermediateField (K₀ k (tE j)) Ω))
    (coordRing k (tE j) (fnFieldE j)) := iR.toModule
  haveI := module_finite_ringMap (tE j) ht (bot_le_fnFieldE j)
  haveI : Algebra.IsIntegral (coordRing k (tE j) (⊥ : IntermediateField (K₀ k (tE j)) Ω))
    (coordRing k (tE j) (fnFieldE j)) := ⟨ringMap_isIntegral _ _⟩
  haveI : FaithfulSMul (coordRing k (tE j) (⊥ : IntermediateField (K₀ k (tE j)) Ω))
      (coordRing k (tE j) (fnFieldE j)) := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact ringMap_injective _ _
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := coordRing k (tE j) (fnFieldE j)) v
  have hex : ∃ P : Ideal (coordRing k (tE j) (fnFieldE j)), P.IsPrime ∧ P.LiesOver v :=
    ⟨P, hP.isPrime, hPl⟩
  unfold multE
  rw [Ideal.ramificationIdxIn, dif_pos hex]
  have := hex.choose_spec.1
  exact Ideal.ramificationIdx_pos _ _

lemma multE_finite :
    {v : Ideal (coordRing k (tE j) (⊥ : IntermediateField (K₀ k (tE j)) Ω)) |
      v.IsMaximal ∧ multE j v ≠ 1}.Finite :=
  finite_ramified (tE j) (transcendental_tE j) (bot_le_fnFieldE j)

/-- **`(E ∖ {0}) / {±1}` as a subfield orbicurve**: the `t`-line with stabilizer orders the
ramification indices of `k(E) / k(t)`. -/
noncomputable def hemiE : AffOrbicurve k :=
  ofSubfield (tE j) (transcendental_tE j) ⊥ (multE j) (multE_pos j) (multE_finite j)

/-- **The quotient map `E ∖ {0} → (E ∖ {0}) / {±1}`**. -/
noncomputable def homE :
    Hom (ofSubfieldScheme (tE j) (transcendental_tE j) (fnFieldE j)) (hemiE j) :=
  homOfLE (transcendental_tE j) (bot_le_fnFieldE j) (fun w hw => by
    rw [mul_one]
    exact multE_eq j w)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The stabilizer orders of `(E ∖ {0}) / {±1}` on both sides agree. -/
lemma ramificationIdxIn_punctured_eq_multE (w : Ideal k[X]) [hw : w.IsMaximal] :
    w.ramificationIdxIn (puncturedRing E) =
      multE j (w.comap (coordRingBotEquiv (transcendental_tE j)).symm.toRingEquiv.toRingHom) := by
  have ht := transcendental_tE j
  set e := coordRingBotEquiv (Ω := Ω) ht
  haveI : IsDedekindDomain (puncturedRing E) := (punctured E).isDedekindDomain
  haveI := isDedekindDomain_ring (tE j) ht (⊥ : IntermediateField (K₀ k (tE j)) Ω)
  haveI := isDedekindDomain_ring (tE j) ht (fnFieldE j)
  have hex : ∃ P : Ideal (puncturedRing E), P.IsPrime ∧ P.LiesOver w := by
    obtain ⟨P, hP, hPl⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := puncturedRing E) w
    exact ⟨P, hP.isPrime, hPl⟩
  rw [Ideal.ramificationIdxIn, dif_pos hex]
  obtain ⟨hP, hPl⟩ := hex.choose_spec
  set P := hex.choose
  haveI := hP
  haveI := hPl
  haveI hPm : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P w
  have hcompat : ∀ r : k[X], puncturedEquiv j (algebraMap k[X] (puncturedRing E) r) =
      (ringMap (tE j) (bot_le_fnFieldE j)).toRingHom (e r) := by
    intro r
    apply Subtype.ext; apply Subtype.ext
    rw [coe_puncturedEquiv]
    change j (algebraMap k[X] E.toAffine.FunctionField r) = _
    rw [j_algebraMap_poly, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_ringMap,
      coe_coordRingBotEquiv]
  have hcongr := ramificationIdx_congr (algebraMap k[X] (puncturedRing E))
    (ringMap (tE j) (bot_le_fnFieldE j)).toRingHom e.toRingEquiv (puncturedEquiv j) hcompat
    (ringMap_injective _ _) P
  have halg : (algebraMap k[X] (puncturedRing E)).toAlgebra =
      (inferInstance : Algebra k[X] (puncturedRing E)) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  rw [halg] at hcongr
  rw [hcongr]
  set ŵ := P.comap (puncturedEquiv j).symm.toRingHom
  haveI : ŵ.IsMaximal := Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective _)
  refine (multE_eq j ŵ).trans (congrArg _ ?_)
  ext x
  obtain ⟨r, rfl⟩ := e.surjective x
  simp only [Ideal.mem_comap]
  change (puncturedEquiv j).symm ((ringMap (tE j) (bot_le_fnFieldE j)).toRingHom (e r)) ∈ P ↔
    e.symm (e r) ∈ w
  rw [← hcompat, RingEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, hPl.over]
  rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **`(E ∖ {0}) / {±1}` as a subfield orbicurve.** -/
noncomputable def isoHemiE : Iso (hemiE j) (hemi E) :=
  Iso.ofAlgEquiv (X := hemiE j) (Y := hemi E) (coordRingBotEquiv (transcendental_tE j)).symm
    (fun w hw => @ramificationIdxIn_punctured_eq_multE k _ E Ω _ _ j _ _ _ w hw)

end AffOrbicurve
