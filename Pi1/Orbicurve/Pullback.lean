module

public import Pi1.Orbicurve.SubfieldGalois
public import Pi1.Orbicurve.TameInertia
public import Pi1.Orbicurve.Morphisms
public import Pi1.Orbicurve.Embed

/-!
# Pullbacks of finite étale covers of subfield orbicurves

Let `Ω` be algebraically closed and normal over `K₀ = k(t)` (characteristic `0`). For the
finite étale cover `ofSubfield A m_A → ofSubfield B m_B` induced by `B ⊆ A`, every finite étale
`Z → ofSubfield B m_B` is dominated by a finite étale cover of `ofSubfield A m_A`
(`pullback_ofSubfield`): `Z` is `ofSubfield L_Z m_Z` for some `L_Z ⊇ B` (`Pi1.Orbicurve.Embed`),
and the compositum `L_Z ⊔ A` with multiplicities `m(w) = m_B(v) / e(w | v)` is finite étale over
both. The key input is that `e(w | v)` divides `m_B(v)`, since the inertia groups are cyclic
(tame ramification, `Pi1.Orbicurve.TameInertia`) and the ramification indices of `L_Z` and `A`
over `B` divide `m_B(v)` (`ramificationIdx_sup_dvd`). Consequently, orbicurves related by such a
cover have the same `k`-cores (`isCoreOf_ofSubfield_iff`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

section Group

/-- In a finite cyclic group, if two subgroups have index dividing `m`, so does their
intersection. -/
lemma index_inf_dvd_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H₁ H₂ : Subgroup C} {m : ℕ} (h₁ : H₁.index ∣ m) (h₂ : H₂.index ∣ m) :
    (H₁ ⊓ H₂).index ∣ m := by
  letI := IsCyclic.commGroup (α := C)
  have hmem : ∀ g : C, g ^ m ∈ H₁ ⊓ H₂ := by
    intro g
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    haveI : H₁.Normal := Subgroup.normal_of_isMulCommutative H₁
    haveI : H₂.Normal := Subgroup.normal_of_isMulCommutative H₂
    refine ⟨?_, ?_⟩
    · rw [ha, pow_mul]; exact H₁.pow_mem (H₁.pow_index_mem g) a
    · rw [hb, pow_mul]; exact H₂.pow_mem (H₂.pow_index_mem g) b
  haveI : (H₁ ⊓ H₂).Normal := Subgroup.normal_of_isMulCommutative _
  haveI : IsCyclic (C ⧸ (H₁ ⊓ H₂)) :=
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  rw [Subgroup.index, ← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  rintro ⟨g⟩
  change ((g ^ m : C) : C ⧸ (H₁ ⊓ H₂)) = 1
  rw [QuotientGroup.eq_one_iff]
  exact hmem g

/-- A version of `index_inf_dvd_of_isCyclic` for subgroups of a cyclic subgroup, in terms of
cardinalities. -/
lemma dvd_of_card_inf {G : Type*} [Group G] [Finite G] {C H₁ H₂ : Subgroup G} [IsCyclic C]
    (h₁ : H₁ ≤ C) (h₂ : H₂ ≤ C) {d₁ d₂ e m : ℕ}
    (hd₁ : d₁ * Nat.card H₁ = Nat.card C) (hd₂ : d₂ * Nat.card H₂ = Nat.card C)
    (he : e * Nat.card (H₁ ⊓ H₂ : Subgroup G) = Nat.card C) (hm₁ : d₁ ∣ m) (hm₂ : d₂ ∣ m) :
    e ∣ m := by
  have key : ∀ {H : Subgroup G} {d : ℕ}, H ≤ C → d * Nat.card H = Nat.card C →
      (H.subgroupOf C).index = d := by
    intro H d hH hd
    have h1 := (H.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv] at h1
    have hpos : 0 < Nat.card H := Nat.card_pos
    rw [← hd, mul_comm d] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have k₁ := key h₁ hd₁
  have k₂ := key h₂ hd₂
  have k := key (inf_le_left.trans h₁) he
  have hinf : (H₁ ⊓ H₂).subgroupOf C = H₁.subgroupOf C ⊓ H₂.subgroupOf C := by
    ext x; simp [Subgroup.mem_subgroupOf]
  rw [hinf] at k
  rw [← k]
  exact index_inf_dvd_of_isCyclic (k₁ ▸ hm₁) (k₂ ▸ hm₂)

end Group

/-- A ring isomorphism is unramified. -/
lemma ramificationIdx_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A]
    [IsDedekindDomain B] (ψ : A ≃+* B) (w : Ideal B) [w.IsPrime] :
    (letI := ψ.toRingHom.toAlgebra; w.ramificationIdx A) = 1 := by
  have h := ramificationIdx_comp ψ.toRingHom ψ.symm.toRingHom ψ.symm.injective
    (w.comap ψ.toRingHom)
  have hw : (w.comap ψ.toRingHom).comap ψ.symm.toRingHom = w := by
    ext x
    simp only [Ideal.mem_comap]
    change ψ (ψ.symm x) ∈ w ↔ x ∈ w
    rw [RingEquiv.apply_symm_apply]
  have hid : ψ.symm.toRingHom.comp ψ.toRingHom = RingHom.id A := by
    ext x; simp
  rw [hw, hid] at h
  haveI : (w.comap ψ.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  have h1 : (letI := (RingHom.id A).toAlgebra; (w.comap ψ.toRingHom).ramificationIdx A) = 1 := by
    have halg : (RingHom.id A).toAlgebra = Algebra.id A := Algebra.algebra_ext _ _ (fun _ => rfl)
    rw [halg]
    exact Ideal.ramificationIdx_eq_one _ A
  rw [h1] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

section Galois

variable {N : IntermediateField (K₀ k t) Ω}

/-- `Gal(N / L ⊔ L') = Gal(N / L) ∩ Gal(N / L')`. -/
lemma fixSub_sup {L L' : IntermediateField (K₀ k t) Ω} (hL : L ≤ N) (hL' : L' ≤ N) :
    fixSub t N (L ⊔ L') = fixSub t N L ⊓ fixSub t N L' := by
  refine le_antisymm (le_inf (fixSub_antitone t le_sup_left) (fixSub_antitone t le_sup_right)) ?_
  rintro σ ⟨hσ, hσ'⟩
  let S : IntermediateField (K₀ k t) Ω :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).map N.val
  have hS : ∀ {F : IntermediateField (K₀ k t) Ω}, F ≤ N → (∀ x : N, (x : Ω) ∈ F → σ x = x) →
      F ≤ S := by
    intro F hFN hF y hy
    refine ⟨⟨y, hFN hy⟩, ?_, rfl⟩
    rintro ⟨τ, n, rfl⟩
    change (σ ^ n) _ = _
    induction n using Int.induction_on with
    | zero => rfl
    | succ n ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, hF _ hy]; exact ih
    | pred n ih =>
      rw [zpow_sub_one, AlgEquiv.mul_apply]
      have : σ⁻¹ ⟨y, hFN hy⟩ = ⟨y, hFN hy⟩ := by
        conv_lhs => rw [← hF ⟨y, hFN hy⟩ hy]
        exact σ.symm_apply_apply _
      rw [this]; exact ih
  intro x hx
  obtain ⟨z, hz, hzx⟩ := sup_le (hS hL hσ) (hS hL' hσ') hx
  have : z = x := Subtype.ext hzx
  subst this
  exact (IntermediateField.mem_fixedField_iff _ _).mp hz σ (Subgroup.mem_zpowers σ)

variable (N) [FiniteDimensional (K₀ k t) N] [IsGalois (K₀ k t) N]

omit [IsGalois (K₀ k t) N] in
/-- `Gal(N / K₀)` acts faithfully on the coordinate ring of `N`. -/
lemma faithfulSMul_coordRing : FaithfulSMul (N ≃ₐ[K₀ k t] N) (coordRing k t N) := by
  refine ⟨fun {σ τ} h => ?_⟩
  have hc : ∀ (ρ : N ≃ₐ[K₀ k t] N) (b : coordRing k t N), ((ρ • b : coordRing k t N) : N) = ρ b :=
    fun _ _ => rfl
  have hb : ∀ b : coordRing k t N, σ (b : N) = τ b := fun b => by
    rw [← hc, ← hc, h b]
  haveI := isFractionRing_coordRing t N
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := coordRing k t N) x
  rw [map_div₀, map_div₀]
  exact congrArg Subtype.val (congrArg₂ (· / ·) (hb a) (hb b))

variable [CharZero k]

/-- **Tame inertia is cyclic**: the inertia groups of `Gal(N / K₀)` at the maximal ideals of the
coordinate ring of `N` are cyclic (characteristic `0`). -/
theorem isCyclic_inertia_coordRing (ht : Transcendental k t) (u : Ideal (coordRing k t N))
    [u.IsMaximal] (hu0 : u ≠ ⊥) : IsCyclic (u.inertia (N ≃ₐ[K₀ k t] N)) := by
  haveI := isDedekindDomain_ring t ht N
  haveI := faithfulSMul_coordRing t N
  haveI : CharZero (IsLocalRing.ResidueField (Localization.AtPrime u)) :=
    charZero_of_injective_algebraMap
      (algebraMap k (IsLocalRing.ResidueField (Localization.AtPrime u))).injective
  exact TameInertia.isCyclic_inertia u hu0

variable {N}

/-- **Ramification in a compositum** (tame, characteristic `0`): for `F ⊆ L₁, L₂ ⊆ N`, if the
ramification indices of `L₁` and `L₂` over `F` at the primes under `u` divide `m`, so does that of
`L₁ ⊔ L₂` (the inertia group is cyclic). -/
theorem ramificationIdx_sup_dvd (ht : Transcendental k t) {F L₁ L₂ : IntermediateField (K₀ k t) Ω}
    (h₁ : F ≤ L₁) (h₂ : F ≤ L₂) (hN₁ : L₁ ≤ N) (hN₂ : L₂ ≤ N) (u : Ideal (coordRing k t N))
    [u.IsMaximal] (hu0 : u ≠ ⊥) {m : ℕ}
    (hm₁ : (letI := algRing t h₁; (u.comap (ringMap t hN₁)).ramificationIdx (coordRing k t F)) ∣ m)
    (hm₂ : (letI := algRing t h₂; (u.comap (ringMap t hN₂)).ramificationIdx (coordRing k t F)) ∣
      m) :
    (letI := algRing t (h₁.trans (le_sup_left : L₁ ≤ L₁ ⊔ L₂));
      (u.comap (ringMap t (sup_le hN₁ hN₂))).ramificationIdx (coordRing k t F)) ∣ m := by
  haveI := isCyclic_inertia_coordRing t N ht u hu0
  set I := u.inertia (N ≃ₐ[K₀ k t] N)
  haveI : IsCyclic (I ⊓ fixSub t N F : Subgroup _) :=
    isCyclic_of_injective (Subgroup.inclusion (inf_le_left : I ⊓ fixSub t N F ≤ I))
      (Subgroup.inclusion_injective _)
  have e₁ := ramificationIdx_mul_card t ht h₁ hN₁ u
  have e₂ := ramificationIdx_mul_card t ht h₂ hN₂ u
  have e' := ramificationIdx_mul_card t ht (h₁.trans (le_sup_left : L₁ ≤ L₁ ⊔ L₂))
    (sup_le hN₁ hN₂) u
  rw [fixSub_sup t hN₁ hN₂, inf_inf_distrib_left] at e'
  exact dvd_of_card_inf (inf_le_inf_left _ (fixSub_antitone t h₁))
    (inf_le_inf_left _ (fixSub_antitone t h₂)) e₁ e₂ e' hm₁ hm₂

end Galois

lemma ringMap_comp {L₁ L₂ L₃ : IntermediateField (K₀ k t) Ω} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃) :
    (ringMap t h₂).comp (ringMap t h₁) = ringMap t (h₁.trans h₂) := rfl

/-- Arithmetic for the multiplicities of a pullback. -/
lemma mul_div_eq_of_dvd {e₁ eA mA mB : ℕ} (hA : eA * mA = mB) (hpos : 0 < mB)
    (hdvd : eA * e₁ ∣ mB) : e₁ * (mB / (eA * e₁)) = mA := by
  rw [mul_comm eA] at hdvd ⊢
  subst hA
  have heA : 0 < eA := Nat.pos_of_ne_zero fun h => by simp [h] at hpos
  have h1 : e₁ ∣ mA := by
    rw [mul_comm e₁] at hdvd
    exact (Nat.mul_dvd_mul_iff_left heA).mp hdvd
  rw [mul_comm e₁ eA, Nat.mul_div_mul_left _ _ heA, Nat.mul_div_cancel' h1]

section Pullback

variable [CharZero k] [Normal (K₀ k t) Ω] (ht : Transcendental k t)

include ht in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Pullbacks of finite étale covers of subfield orbicurves**: given finite étale covers
`ofSubfield A m_A → ofSubfield B m_B` and `ofSubfield Z m_Z → ofSubfield B m_B` induced by
`B ⊆ A` and `B ⊆ Z`, the compositum `L = Z ⊔ A`, with multiplicities `m(w) = m_B(v) / e(w | v)`,
is finite étale over both (a component of the fibre product; tame ramification). -/
theorem exists_pullback_subfield {B A Z : IntermediateField (K₀ k t) Ω}
    [FiniteDimensional (K₀ k t) B] [FiniteDimensional (K₀ k t) A] [FiniteDimensional (K₀ k t) Z]
    (hBA : B ≤ A) (hBZ : B ≤ Z) (mB : Ideal (coordRing k t B) → ℕ)
    (mB_pos : ∀ v, v.IsMaximal → 0 < mB v)
    (mB_fin : {v : Ideal (coordRing k t B) | v.IsMaximal ∧ mB v ≠ 1}.Finite)
    (mA : Ideal (coordRing k t A) → ℕ) (mZ : Ideal (coordRing k t Z) → ℕ)
    (hA : ∀ w : Ideal (coordRing k t A), w.IsMaximal →
      (letI := algRing t hBA; w.ramificationIdx (coordRing k t B)) * mA w =
        mB (w.comap (ringMap t hBA)))
    (hZ : ∀ w : Ideal (coordRing k t Z), w.IsMaximal →
      (letI := algRing t hBZ; w.ramificationIdx (coordRing k t B)) * mZ w =
        mB (w.comap (ringMap t hBZ))) :
    ∃ (m : Ideal (coordRing k t (Z ⊔ A)) → ℕ),
      (∀ w, w.IsMaximal → 0 < m w) ∧
      {w : Ideal (coordRing k t (Z ⊔ A)) | w.IsMaximal ∧ m w ≠ 1}.Finite ∧
      (∀ w : Ideal (coordRing k t (Z ⊔ A)), w.IsMaximal →
        (letI := algRing t (le_sup_left : Z ≤ Z ⊔ A); w.ramificationIdx (coordRing k t Z)) * m w =
          mZ (w.comap (ringMap t le_sup_left))) ∧
      (∀ w : Ideal (coordRing k t (Z ⊔ A)), w.IsMaximal →
        (letI := algRing t (le_sup_right : A ≤ Z ⊔ A); w.ramificationIdx (coordRing k t A)) * m w =
          mA (w.comap (ringMap t le_sup_right))) := by
  set L := Z ⊔ A
  have hBL : B ≤ L := hBZ.trans le_sup_left
  haveI : FiniteDimensional (K₀ k t) L := IntermediateField.finiteDimensional_sup Z A
  haveI : CharZero (K₀ k t) := charZero_of_injective_algebraMap (algebraMap k (K₀ k t)).injective
  let N := IntermediateField.normalClosure (K₀ k t) L Ω
  have hLN : L ≤ N := IntermediateField.le_normalClosure L
  haveI : IsGalois (K₀ k t) N := by
    haveI : Algebra.IsSeparable (K₀ k t) N := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsGalois.mk
  let eL : Ideal (coordRing k t L) → ℕ := fun w =>
    letI := algRing t hBL; w.ramificationIdx (coordRing k t B)
  haveI := isDedekindDomain_ring t ht B
  haveI := isDedekindDomain_ring t ht A
  haveI := isDedekindDomain_ring t ht Z
  haveI := isDedekindDomain_ring t ht L
  haveI := isDedekindDomain_ring t ht N
  -- comaps of maximal ideals are maximal
  have hmax : ∀ {F F' : IntermediateField (K₀ k t) Ω} (h : F ≤ F') (w : Ideal (coordRing k t F')),
      w.IsMaximal → (w.comap (ringMap t h)).IsMaximal := by
    intro F F' h w hw
    letI := algRing t h
    haveI : Algebra.IsIntegral (coordRing k t F) (coordRing k t F') := ⟨ringMap_isIntegral t h⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := coordRing k t F) w
  -- the key divisibility
  have hdiv : ∀ w : Ideal (coordRing k t L), w.IsMaximal →
      eL w ∣ mB (w.comap (ringMap t hBL)) := by
    intro w hw
    obtain ⟨u, hu, hul⟩ : ∃ u : Ideal (coordRing k t N), u.IsMaximal ∧
        u.comap (ringMap t hLN) = w := by
      letI := algRing t hLN
      haveI : Algebra.IsIntegral (coordRing k t L) (coordRing k t N) :=
        ⟨ringMap_isIntegral _ hLN⟩
      haveI : FaithfulSMul (coordRing k t L) (coordRing k t N) := by
        rw [faithfulSMul_iff_algebraMap_injective]; exact ringMap_injective _ hLN
      obtain ⟨u, hu, hul⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
        (S := coordRing k t N) w
      exact ⟨u, hu, hul.over.symm⟩
    subst hul
    have hu0 : u ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hu (not_isField_ring t ht N)
    have hZN : Z ≤ N := le_sup_left.trans hLN
    have hAN : A ≤ N := le_sup_right.trans hLN
    have h₁ := hZ _ (hmax hZN u hu)
    have h₂ := hA _ (hmax hAN u hu)
    have hv₁ : (u.comap (ringMap t hZN)).comap (ringMap t hBZ) =
        (u.comap (ringMap t hLN)).comap (ringMap t hBL) := rfl
    have hv₂ : (u.comap (ringMap t hAN)).comap (ringMap t hBA) =
        (u.comap (ringMap t hLN)).comap (ringMap t hBL) := rfl
    rw [hv₁] at h₁
    rw [hv₂] at h₂
    exact ramificationIdx_sup_dvd t ht hBZ hBA hZN hAN u hu0 (Dvd.intro _ h₁) (Dvd.intro _ h₂)
  -- the etale condition over an intermediate field
  have hetale : ∀ {F : IntermediateField (K₀ k t) Ω} [FiniteDimensional (K₀ k t) F]
      (hBF : B ≤ F) (hFL : F ≤ L) (mF : Ideal (coordRing k t F) → ℕ)
      (_hF : ∀ w : Ideal (coordRing k t F), w.IsMaximal →
        (letI := algRing t hBF; w.ramificationIdx (coordRing k t B)) * mF w =
          mB (w.comap (ringMap t hBF))) (w : Ideal (coordRing k t L)), w.IsMaximal →
      (letI := algRing t hFL; w.ramificationIdx (coordRing k t F)) *
        (mB (w.comap (ringMap t hBL)) / eL w) = mF (w.comap (ringMap t hFL)) := by
    intro F _ hBF hFL mF hF w hw
    haveI := isDedekindDomain_ring t ht F
    have htower := ramificationIdx_comp (ringMap t hBF).toRingHom (ringMap t hFL).toRingHom
      (ringMap_injective t hFL) w
    have hF' := hF _ (hmax hFL w hw)
    have hv : (w.comap (ringMap t hFL)).comap (ringMap t hBF) = w.comap (ringMap t hBL) := rfl
    rw [hv] at hF'
    have heL : eL w = (letI := algRing t hBF;
        (w.comap (ringMap t hFL)).ramificationIdx (coordRing k t B)) *
        (letI := algRing t hFL; w.ramificationIdx (coordRing k t F)) := htower
    have hd := hdiv w hw
    rw [heL] at hd ⊢
    exact mul_div_eq_of_dvd hF' (mB_pos _ (hmax hBL w hw)) hd
  refine ⟨fun w => mB (w.comap (ringMap t hBL)) / eL w, ?_, ?_,
    hetale hBZ le_sup_left mZ hZ, hetale hBA le_sup_right mA hA⟩
  · intro w hw
    have hd := hdiv w hw
    have hpos := mB_pos _ (hmax hBL w hw)
    have he : 0 < eL w := Nat.pos_of_ne_zero fun h => by
      rw [h, zero_dvd_iff] at hd; omega
    exact Nat.div_pos (Nat.le_of_dvd hpos hd) he
  · letI := algRing t hBL
    haveI : Algebra.IsIntegral (coordRing k t B) (coordRing k t L) := ⟨ringMap_isIntegral t hBL⟩
    haveI : Module.IsTorsionFree (coordRing k t B) (coordRing k t L) := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]; exact ringMap_injective t hBL
    refine (mB_fin.biUnion (t := fun v => v.primesOver (coordRing k t L)) fun v hv => ?_).subset ?_
    · haveI := hv.1
      exact IsDedekindDomain.primesOver_finite v (coordRing k t L)
    · rintro w ⟨hw, hne⟩
      refine Set.mem_biUnion (x := w.comap (ringMap t hBL)) ⟨hmax hBL w hw, fun h1 => hne ?_⟩
        ⟨hw.isPrime, ⟨rfl⟩⟩
      have hd := hdiv w hw
      simp only [h1, Nat.dvd_one] at hd ⊢
      rw [hd]

variable [IsAlgClosed Ω]

include ht in
set_option maxHeartbeats 1000000 in
/-- **Pullbacks of finite étale covers of subfield orbicurves**: if `ofSubfield A m_A →
ofSubfield B m_B` is the finite étale cover induced by `B ⊆ A`, every finite étale cover
`Z → ofSubfield B m_B` is dominated by a finite étale cover of `ofSubfield A m_A` (a component
of `Z ×_B A`). -/
theorem pullback_ofSubfield {B A : IntermediateField (K₀ k t) Ω}
    [FiniteDimensional (K₀ k t) B] [Algebra.IsSeparable (K₀ k t) B]
    [FiniteDimensional (K₀ k t) A] [Algebra.IsSeparable (K₀ k t) A]
    (hBA : B ≤ A) {mB : Ideal (coordRing k t B) → ℕ} {mB_pos mB_fin}
    {mA : Ideal (coordRing k t A) → ℕ} {mA_pos mA_fin}
    (hA : ∀ w : Ideal (coordRing k t A), w.IsMaximal →
      (letI := algRing t hBA; w.ramificationIdx (coordRing k t B)) * mA w =
        mB (w.comap (ringMap t hBA)))
    (Z : AffOrbicurve k) (φ : Hom Z (ofSubfield t ht B mB mB_pos mB_fin)) :
    ∃ Z' : AffOrbicurve k, Nonempty (Hom Z' Z) ∧
      Nonempty (Hom Z' (ofSubfield t ht A mA mA_pos mA_fin)) := by
  haveI : CharZero (K₀ k t) := charZero_of_injective_algebraMap (algebraMap k (K₀ k t)).injective
  obtain ⟨LZ, _, hBZ, ψ, hψ⟩ := exists_algEquiv_coordRing t Z.A φ.f φ.injective φ.isIntegral
  haveI : Algebra.IsSeparable (K₀ k t) LZ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI := isDedekindDomain_ring t ht LZ
  -- `Z` as a subfield orbicurve
  let mZ : Ideal (coordRing k t LZ) → ℕ := fun w => Z.mult (w.comap ψ)
  have hcomap_max : ∀ w : Ideal (coordRing k t LZ), w.IsMaximal → (w.comap ψ).IsMaximal :=
    fun w hw => Ideal.comap_isMaximal_of_surjective ψ ψ.surjective
  have mZ_pos : ∀ w, w.IsMaximal → 0 < mZ w := fun w hw => Z.mult_pos _ (hcomap_max w hw)
  have mZ_fin : {w : Ideal (coordRing k t LZ) | w.IsMaximal ∧ mZ w ≠ 1}.Finite := by
    refine (Z.finite_mult.image fun v => v.comap ψ.symm).subset ?_
    rintro w ⟨hw, hne⟩
    refine ⟨w.comap ψ, ⟨hcomap_max w hw, hne⟩, ?_⟩
    ext x
    simp only [Ideal.mem_comap]
    rw [AlgEquiv.apply_symm_apply]
  let ZL := ofSubfield t ht LZ mZ mZ_pos mZ_fin
  let hZLZ : Hom ZL Z :=
    { f := ψ.toAlgHom
      injective := ψ.injective
      isIntegral := RingHom.IsIntegral.of_finite (RingHom.Finite.of_surjective _ ψ.surjective)
      etale := fun w hw => by
        have h1 :=
          @ramificationIdx_ringEquiv Z.A (coordRing k t LZ) _ _ _ _ ψ.toRingEquiv w hw.isPrime
        exact (congrArg (· * mZ w) h1).trans (one_mul _) }
  have hZ : ∀ w : Ideal (coordRing k t LZ), w.IsMaximal →
      (letI := algRing t hBZ; w.ramificationIdx (coordRing k t B)) * mZ w =
        mB (w.comap (ringMap t hBZ)) := by
    intro w hw
    have h := (hZLZ.comp φ).etale w hw
    have hf : (hZLZ.comp φ).f = ringMap t hBZ := AlgHom.ext hψ
    rw [hf] at h
    exact h
  obtain ⟨m, m_pos, m_fin, hmZ, hmA⟩ :=
    exists_pullback_subfield t ht hBA hBZ mB mB_pos mB_fin mA mZ hA hZ
  haveI : FiniteDimensional (K₀ k t) ↥(LZ ⊔ A) := IntermediateField.finiteDimensional_sup LZ A
  haveI : Algebra.IsSeparable (K₀ k t) ↥(LZ ⊔ A) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨ofSubfield t ht (LZ ⊔ A) m m_pos m_fin,
    ⟨(homOfLE ht le_sup_left hmZ).comp hZLZ⟩, ⟨homOfLE ht le_sup_right hmA⟩⟩

include ht in
/-- **Finite étale covers of subfield orbicurves have the same cores**: for the finite étale cover
`ofSubfield A m_A → ofSubfield B m_B` induced by `B ⊆ A`, `C` is the `k`-core of the one iff it is
the `k`-core of the other. -/
theorem isCoreOf_ofSubfield_iff {B A : IntermediateField (K₀ k t) Ω}
    [FiniteDimensional (K₀ k t) B] [Algebra.IsSeparable (K₀ k t) B]
    [FiniteDimensional (K₀ k t) A] [Algebra.IsSeparable (K₀ k t) A]
    (hBA : B ≤ A) {mB : Ideal (coordRing k t B) → ℕ} {mB_pos mB_fin}
    {mA : Ideal (coordRing k t A) → ℕ} {mA_pos mA_fin}
    (hA : ∀ w : Ideal (coordRing k t A), w.IsMaximal →
      (letI := algRing t hBA; w.ramificationIdx (coordRing k t B)) * mA w =
        mB (w.comap (ringMap t hBA)))
    (C : AffOrbicurve k) :
    IsCoreOf (ofSubfield t ht A mA mA_pos mA_fin) C ↔
      IsCoreOf (ofSubfield t ht B mB mB_pos mB_fin) C :=
  ⟨IsCoreOf.of_hom_of_pullback (homOfLE ht hBA hA)
    (fun Z φ => pullback_ofSubfield t ht hBA hA Z φ),
   IsCoreOf.of_hom (homOfLE ht hBA hA)⟩

end Pullback

end AffOrbicurve
