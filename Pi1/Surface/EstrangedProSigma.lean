/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.SlimProSigma
public import Pi1.Surface.Commensurator

/-!
# Pro-`Σ` cusp inertia groups are malnormal ("totally estranged")

Let `Σ` be a set of primes (a predicate `P`; no hypothesis on `P` is needed: if `Σ` contains no
prime, all pro-`Σ` completions are trivial). For an element `γ` of a group `Γ`, the
**pro-`Σ` inertia group** `ProSigmaCompletion.inertiaSigma P γ ⊆ Γ^Σ` is the image of
`ℤ^Σ → Γ^Σ`, `1 ↦ γ`; for the cusp generators of the surface group this is the range of
`SurfaceGroup.cuspInertiaSigma`. We prove:

* `ProSigmaCompletion.eq_one_of_forall_liftFinite`: the extensions of homomorphisms to finite
  groups of `Σ`-integer order separate the points of `Γ^Σ`;
* `ProSigmaCompletion.mem_inertiaSigma_of`: membership in `inertiaSigma P γ` is detected by
  finite quotients of `Σ`-integer order;
* for a basis element `a` of a free group: `inertiaSigma_inf_conj_eq_bot_of_ne` (distinct basis
  elements) and `mem_inertiaSigma_of_commute` (the centraliser of a non-trivial element of
  `inertiaSigma P a` lies in it), hence `inertiaSigma_inf_conj_eq_bot_self`;
* **`SurfaceGroup.cuspInertiaSigma_inf_conj_eq_bot`**: for at least three cusps and `i ≠ j`,
  `I_i ∩ σ I_j σ⁻¹ = 1` in `Π^Σ_{g,r}`;
* **`SurfaceGroup.cuspInertiaSigma_inf_conj_eq_bot_self`**: for at least two cusps and
  `σ ∉ I_k`, `I_k ∩ σ I_k σ⁻¹ = 1`.

Together these are the condition "estranged" of [SemiAnbd] Def 2.4(iv) (`Semi-graphs of
Anabelioids.txt` l.1138–1143: for a branch `b` abutting a vertex `v` and `g ∈ Π_v`, the
intersection of `Π_b` with `g · Π_b' · g⁻¹` is trivial, where either `b' ≠ b` is a branch abutting
`v`, or `b' = b` and `g ∉ Π_b`) at a vertex with vertex group `Π^Σ_{g,r}` whose branch groups are
cusp inertia groups, the situation of [SemiAnbd] Ex 2.10 (l.1433–1446, which refers to the proof
of [Mzk3] Lemma 1.3.7); `SurfaceGroup.cuspInertiaSigma_estranged_zero_three` collects the case of
a vertex of type `(0, 3)` (the vertex of the stable `1`-gon of MR12 T3). The proof is the
argument of `Pi1.Profinite.Commensurator` (abelian characters `χ_N` and the wreath product
`(ℤ/ℓ) ≀ Q`) carried out with finite quotients of `Σ`-integer order, with one change: a
non-trivial element `z` of `inertiaSigma P a` is a `Σ`-adic (not an integral) power of `a`, so
the prime `ℓ ∈ Σ` and the power `z ^ M` lying in the kernel of the finite quotient are chosen
from a character `χ_N` with `χ_N(z) ≠ 1`.
-/

@[expose] public section

open Topology
open scoped Pointwise

namespace Pi1

/-! ### Conjugates of subgroups -/

section Conj

variable {G H : Type*} [Group G] [Group H]

lemma mem_toConjAct_smul_iff {B : Subgroup G} {σ z : G} :
    z ∈ ConjAct.toConjAct σ • B ↔ σ⁻¹ * z * σ ∈ B := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
    ConjAct.ofConjAct_toConjAct, inv_inv]

lemma map_conj_eq_toConjAct_smul (B : Subgroup G) (c : G) :
    B.map (MulAut.conj c).toMonoidHom = ConjAct.toConjAct c • B := by
  ext z
  rw [mem_toConjAct_smul_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hz
    exact ⟨c⁻¹ * z * c, hz, by simp [mul_assoc]⟩

/-- Trivial intersections of conjugates are preserved by isomorphisms. -/
lemma inf_conj_eq_bot_map (e : G ≃* H) {A B : Subgroup G}
    (h : ∀ σ : G, A ⊓ (ConjAct.toConjAct σ • B) = ⊥) (τ : H) :
    A.map e.toMonoidHom ⊓ (ConjAct.toConjAct τ • B.map e.toMonoidHom) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ ?_
  obtain ⟨hzA, hzB⟩ := Subgroup.mem_inf.1 hz
  rw [mem_toConjAct_smul_iff] at hzB
  obtain ⟨x, hx, rfl⟩ := hzA
  obtain ⟨y, hy, hxy⟩ := hzB
  have hmem : x ∈ A ⊓ (ConjAct.toConjAct (e.symm τ) • B) := by
    refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
    rw [mem_toConjAct_smul_iff]
    have hyx : (e.symm τ)⁻¹ * x * e.symm τ = y := by
      apply e.injective
      simp only [MulEquiv.coe_toMonoidHom] at hxy
      simp [hxy]
    rw [hyx]
    exact hy
  rw [h, Subgroup.mem_bot] at hmem
  simp [hmem]

/-- Malnormality is preserved by isomorphisms. -/
lemma inf_conj_self_eq_bot_map (e : G ≃* H) {A : Subgroup G}
    (h : ∀ σ : G, σ ∉ A → A ⊓ (ConjAct.toConjAct σ • A) = ⊥) (τ : H)
    (hτ : τ ∉ A.map e.toMonoidHom) :
    A.map e.toMonoidHom ⊓ (ConjAct.toConjAct τ • A.map e.toMonoidHom) = ⊥ := by
  have hτ' : e.symm τ ∉ A := fun h' ↦ hτ ⟨_, h', by simp⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ ?_
  obtain ⟨hzA, hzB⟩ := Subgroup.mem_inf.1 hz
  rw [mem_toConjAct_smul_iff] at hzB
  obtain ⟨x, hx, rfl⟩ := hzA
  obtain ⟨y, hy, hxy⟩ := hzB
  have hmem : x ∈ A ⊓ (ConjAct.toConjAct (e.symm τ) • A) := by
    refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
    rw [mem_toConjAct_smul_iff]
    have hyx : (e.symm τ)⁻¹ * x * e.symm τ = y := by
      apply e.injective
      simp only [MulEquiv.coe_toMonoidHom] at hxy
      simp [hxy]
    rw [hyx]
    exact hy
  rw [h _ hτ', Subgroup.mem_bot] at hmem
  simp [hmem]

/-- Trivial intersections of conjugates are preserved by conjugating both subgroups. -/
lemma inf_conj_eq_bot_conj {A B : Subgroup G} (h : ∀ σ : G, A ⊓ (ConjAct.toConjAct σ • B) = ⊥)
    (c d σ : G) :
    (ConjAct.toConjAct c • A) ⊓ (ConjAct.toConjAct σ • (ConjAct.toConjAct d • B)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ ?_
  obtain ⟨hzA, hzB⟩ := Subgroup.mem_inf.1 hz
  rw [mem_toConjAct_smul_iff] at hzA hzB
  rw [mem_toConjAct_smul_iff] at hzB
  have hmem : c⁻¹ * z * c ∈ A ⊓ (ConjAct.toConjAct (c⁻¹ * σ * d) • B) := by
    refine Subgroup.mem_inf.2 ⟨hzA, ?_⟩
    rw [mem_toConjAct_smul_iff]
    convert hzB using 1
    group
  rw [h, Subgroup.mem_bot] at hmem
  calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
    _ = 1 := by rw [hmem]; group

/-- Malnormality is preserved by conjugation. -/
lemma inf_conj_self_eq_bot_conj {A : Subgroup G}
    (h : ∀ σ : G, σ ∉ A → A ⊓ (ConjAct.toConjAct σ • A) = ⊥) (c τ : G)
    (hτ : τ ∉ ConjAct.toConjAct c • A) :
    (ConjAct.toConjAct c • A) ⊓ (ConjAct.toConjAct τ • (ConjAct.toConjAct c • A)) = ⊥ := by
  rw [mem_toConjAct_smul_iff] at hτ
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ ?_
  obtain ⟨hzA, hzB⟩ := Subgroup.mem_inf.1 hz
  rw [mem_toConjAct_smul_iff] at hzA hzB
  rw [mem_toConjAct_smul_iff] at hzB
  have hmem : c⁻¹ * z * c ∈ A ⊓ (ConjAct.toConjAct (c⁻¹ * τ * c) • A) := by
    refine Subgroup.mem_inf.2 ⟨hzA, ?_⟩
    rw [mem_toConjAct_smul_iff]
    convert hzB using 1
    group
  rw [h _ hτ, Subgroup.mem_bot] at hmem
  calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
    _ = 1 := by rw [hmem]; group

end Conj

namespace Profinite

namespace ProSigmaCompletion

variable {P : ℕ → Prop} {Γ Γ' : Type} [Group Γ] [Group Γ']

/-! ### Separation by finite quotients of `Σ`-integer order -/

theorem liftFinite_comp {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q']
    (f : Γ →* Q) (π : Q →* Q') (hQ : IsSigmaNat P (Nat.card Q))
    (hQ' : IsSigmaNat P (Nat.card Q')) (z : ProSigmaCompletion P Γ) :
    liftFinite (π.comp f) hQ' z = π (liftFinite f hQ z) := by
  obtain ⟨w, hw1, hw2⟩ := exists_eta_mem_of_isOpen
    ((isOpen_liftFinite_fiber (π.comp f) hQ' (liftFinite (π.comp f) hQ' z)).inter
      (isOpen_liftFinite_fiber f hQ (liftFinite f hQ z))) ⟨rfl, rfl⟩
  rw [← hw1, ← hw2, liftFinite_eta, liftFinite_eta, MonoidHom.comp_apply]

/-- `liftFinite` of the quotient map by an open normal subgroup is the quotient map. -/
lemma liftFinite_mk' (M : Subgroup (ProSigmaCompletion P Γ)) [M.Normal]
    (hM : IsOpen (M : Set (ProSigmaCompletion P Γ))) [Finite (ProSigmaCompletion P Γ ⧸ M)]
    (hQ : IsSigmaNat P (Nat.card (ProSigmaCompletion P Γ ⧸ M))) (z : ProSigmaCompletion P Γ) :
    liftFinite ((QuotientGroup.mk' M).comp (eta P)) hQ z = QuotientGroup.mk z := by
  obtain ⟨w, hw1, hw2⟩ := exists_eta_mem_of_isOpen ((isOpen_setOf_mk_eq M hM z).inter
    (isOpen_liftFinite_fiber ((QuotientGroup.mk' M).comp (eta P)) hQ
      (liftFinite ((QuotientGroup.mk' M).comp (eta P)) hQ z))) ⟨rfl, rfl⟩
  rw [← hw2, liftFinite_eta]
  exact hw1

/-- **The extensions of homomorphisms to finite groups of `Σ`-integer order separate the points
of `Γ^Σ`.** -/
theorem eq_one_of_forall_liftFinite {z : ProSigmaCompletion P Γ}
    (h : ∀ (Q : Type) [Group Q] [Finite Q] (f : Γ →* Q) (hQ : IsSigmaNat P (Nat.card Q)),
      liftFinite f hQ z = 1) : z = 1 := by
  by_contra hz1
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := z)) (by simpa [eq_comm] using hz1)
  haveI : Finite (ProSigmaCompletion P Γ ⧸ N.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ N.isOpen
  have hQ := isSigmaNat_index N.toSubgroup N.isOpen
  have := h _ ((QuotientGroup.mk' N.toSubgroup).comp (eta P)) hQ
  rw [liftFinite_mk' _ N.isOpen] at this
  exact hN ((QuotientGroup.eq_one_iff z).1 this) rfl

/-! ### Pro-`Σ` inertia groups -/

variable (P) in
/-- **The pro-`Σ` inertia group** of `γ ∈ Γ`: the image of `ℤ^Σ → Γ^Σ`, `1 ↦ γ`. -/
noncomputable def inertiaSigma (γ : Γ) : Subgroup (ProSigmaCompletion P Γ) :=
  (map (P := P) (zpowersHom Γ γ)).range

lemma eta_mem_inertiaSigma (γ : Γ) : eta P γ ∈ inertiaSigma P γ :=
  ⟨eta P (Multiplicative.ofAdd 1), by rw [map_eta, zpowersHom_apply, toAdd_ofAdd, zpow_one]⟩

/-- Elements of `inertiaSigma P γ` map into `⟨f γ⟩` in every finite quotient of `Σ`-integer
order. -/
theorem liftFinite_mem_zpowers {Q : Type} [Group Q] [Finite Q] (f : Γ →* Q)
    (hQ : IsSigmaNat P (Nat.card Q)) {γ : Γ} {z : ProSigmaCompletion P Γ}
    (hz : z ∈ inertiaSigma P γ) : liftFinite f hQ z ∈ Subgroup.zpowers (f γ) := by
  obtain ⟨x, rfl⟩ := hz
  rw [liftFinite_map]
  obtain ⟨w, hw⟩ := exists_eta_mem_of_isOpen
    (isOpen_liftFinite_fiber (f.comp (zpowersHom _ γ)) hQ
      (liftFinite (f.comp (zpowersHom _ γ)) hQ x)) rfl
  rw [← hw, liftFinite_eta, MonoidHom.comp_apply, zpowersHom_apply, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ _

/-- The same, with a natural exponent. -/
theorem exists_liftFinite_eq_pow {Q : Type} [Group Q] [Finite Q] (f : Γ →* Q)
    (hQ : IsSigmaNat P (Nat.card Q)) {γ : Γ} {z : ProSigmaCompletion P Γ}
    (hz : z ∈ inertiaSigma P γ) : ∃ i : ℕ, liftFinite f hQ z = f γ ^ i := by
  have h := liftFinite_mem_zpowers f hQ hz
  rw [← (isOfFinOrder_of_finite (f γ)).mem_powers_iff_mem_zpowers] at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi.symm⟩

theorem isClosed_inertiaSigma (γ : Γ) :
    IsClosed (inertiaSigma P γ : Set (ProSigmaCompletion P Γ)) := by
  rw [inertiaSigma, MonoidHom.coe_range]
  exact (isCompact_range (continuous_map _)).isClosed

/-- **Membership in `inertiaSigma P γ` is detected by finite quotients of `Σ`-integer order.** -/
theorem mem_inertiaSigma_of {γ : Γ} {z : ProSigmaCompletion P Γ}
    (h : ∀ (Q : Type) [Group Q] [Finite Q] (f : Γ →* Q) (hQ : IsSigmaNat P (Nat.card Q)),
      liftFinite f hQ z ∈ Subgroup.zpowers (f γ)) : z ∈ inertiaSigma P γ := by
  rw [← SetLike.mem_coe, ← (isClosed_inertiaSigma γ).closure_eq, mem_closure_iff_nhds]
  intro U hU
  obtain ⟨V, hVU, hVo, hzV⟩ := mem_nhds_iff.1 hU
  have hV' : IsOpen ((z * ·) ⁻¹' V) := hVo.preimage (continuous_const_mul z)
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV'
    (by simpa using hzV)
  haveI : Finite (ProSigmaCompletion P Γ ⧸ N.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ N.isOpen
  have hQ := isSigmaNat_index N.toSubgroup N.isOpen
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1
    (h _ ((QuotientGroup.mk' N.toSubgroup).comp (eta P)) hQ)
  rw [liftFinite_mk' _ N.isOpen] at hn
  simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply] at hn
  have hmem : z⁻¹ * eta P γ ^ n ∈ N.toSubgroup := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow]
    exact hn.symm
  refine ⟨eta P γ ^ n, hVU ?_, zpow_mem (eta_mem_inertiaSigma γ) n⟩
  simpa using hN hmem

/-- Inertia groups along isomorphisms. -/
theorem inertiaSigma_mulEquiv (e : Γ ≃* Γ') (γ : Γ) :
    inertiaSigma P (e γ) = (inertiaSigma P γ).map (congr (P := P) e).toMulEquiv.toMonoidHom := by
  have h : zpowersHom Γ' (e γ) = e.toMonoidHom.comp (zpowersHom Γ γ) := by
    ext
    simp
  rw [inertiaSigma, inertiaSigma, h, ← map_comp, MonoidHom.range_comp]
  rfl

/-- Inertia groups of conjugates. -/
theorem inertiaSigma_conj (c γ : Γ) :
    inertiaSigma P (c * γ * c⁻¹) = ConjAct.toConjAct (eta P c) • inertiaSigma P γ := by
  have h1 := inertiaSigma_mulEquiv (P := P) (MulAut.conj c) γ
  rw [MulAut.conj_apply] at h1
  rw [h1, ← map_conj_eq_toConjAct_smul]
  congr 1
  have : (congr (P := P) (MulAut.conj c)).toMulEquiv.toMonoidHom =
      map (P := P) (MulAut.conj c).toMonoidHom := rfl
  rw [this]
  have hcont : Continuous (MulAut.conj (eta P c)).toMonoidHom := by
    change Continuous fun y ↦ eta P c * y * (eta P c)⁻¹
    fun_prop
  refine hom_ext (continuous_map _) hcont fun x ↦ ?_
  simp [map_eta]


/-! ### Free groups: abelian characters -/

section Free

variable {α : Type}

lemma isSigmaNat_card_chi {N : ℕ} [NeZero N] (hN : IsSigmaNat P N) :
    IsSigmaNat P (Nat.card (ULift.{0} (Multiplicative (ZMod N)))) := by
  rwa [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-- **Elements of `inertiaSigma P a` are detected by the characters `χ_N`** (`N` a
`Σ`-integer). -/
theorem eq_one_of_mem_of_chi [DecidableEq α] {a : α} {z : ProSigmaCompletion P (FreeGroup α)}
    (hz : z ∈ inertiaSigma P (FreeGroup.of a))
    (hχ : ∀ (N : ℕ) [NeZero N] (hN : IsSigmaNat P N),
      liftFinite (chi a N) (isSigmaNat_card_chi hN) z = 1) : z = 1 := by
  refine eq_one_of_forall_liftFinite fun Q _ _ f hQ ↦ ?_
  set o := orderOf (f (FreeGroup.of a))
  have ho : IsSigmaNat P o := hQ.of_dvd (orderOf_dvd_natCard _)
  haveI : NeZero o := ⟨ho.1⟩
  have hQ' : IsSigmaNat P (Nat.card (Q × ULift.{0} (Multiplicative (ZMod o)))) := by
    rw [Nat.card_prod]
    exact hQ.mul (isSigmaNat_card_chi ho)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1
    (liftFinite_mem_zpowers (f.prod (chi a o)) hQ' hz)
  have h1 : liftFinite f hQ z = f (FreeGroup.of a) ^ i := by
    have := liftFinite_comp (f.prod (chi a o)) (MonoidHom.fst _ _) hQ' hQ z
    rw [MonoidHom.fst_comp_prod] at this
    rw [this, ← hi]
    simp
  have h2 : (chi a o (FreeGroup.of a)) ^ i = 1 := by
    have := liftFinite_comp (f.prod (chi a o)) (MonoidHom.snd _ _) hQ' (isSigmaNat_card_chi ho) z
    rw [MonoidHom.snd_comp_prod, hχ o ho] at this
    rw [this, ← hi]
    simp
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_chi_of_self] at h2
  rw [h1]
  exact orderOf_dvd_iff_zpow_eq_one.1 h2

/-- Conjugates of elements of `inertiaSigma P a` lying in `inertiaSigma P a` are equal to
them. -/
theorem conj_eq_of_mem {a : α} {σ z : ProSigmaCompletion P (FreeGroup α)}
    (hz : z ∈ inertiaSigma P (FreeGroup.of a)) (h : σ⁻¹ * z * σ ∈ inertiaSigma P (FreeGroup.of a)) :
    σ⁻¹ * z * σ = z := by
  classical
  rw [← mul_inv_eq_one]
  refine eq_one_of_mem_of_chi (mul_mem h (inv_mem hz)) fun N _ hN ↦ ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (liftFinite (chi a N) _ σ)⁻¹,
    inv_mul_cancel_right, mul_inv_cancel]

/-- **Inertia groups of distinct basis elements meet trivially**, also after conjugation. -/
theorem inertiaSigma_inf_conj_eq_bot_of_ne {a b : α} (hab : a ≠ b)
    (σ : ProSigmaCompletion P (FreeGroup α)) :
    inertiaSigma P (FreeGroup.of a) ⊓
      (ConjAct.toConjAct σ • inertiaSigma P (FreeGroup.of b)) = ⊥ := by
  classical
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ ?_
  obtain ⟨hza, hzb⟩ := Subgroup.mem_inf.1 hz
  rw [mem_toConjAct_smul_iff] at hzb
  refine eq_one_of_mem_of_chi hza fun N _ hN ↦ ?_
  have h := liftFinite_mem_zpowers (chi a N) (isSigmaNat_card_chi hN) hzb
  rw [chi_of_ne (Ne.symm hab), Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot, map_mul, map_mul,
    map_inv] at h
  set x := liftFinite (chi a N) (isSigmaNat_card_chi hN) σ
  calc liftFinite (chi a N) (isSigmaNat_card_chi hN) z
      = x * (x⁻¹ * liftFinite (chi a N) (isSigmaNat_card_chi hN) z * x) * x⁻¹ := by group
    _ = 1 := by rw [h]; group

end Free

/-! ### Free groups: the centraliser of a non-trivial element of `inertiaSigma P a` -/

section Centraliser

open WreathMod

variable {α : Type}

/-- The projection `(ℤ/n) ≀ Q → Q`. -/
def wrTop (Q : Type) [Group Q] (n : ℕ) : WreathMod.wrSub Q n →* Q where
  toFun x := (x.1 (1, 0)).1
  map_one' := rfl
  map_mul' := by
    rintro ⟨_, q, f, rfl⟩ ⟨_, q', f', rfl⟩
    simp

lemma wrTop_wr {Q : Type} [Group Q] {n : ℕ} (q : Q) (f : Q → ZMod n) :
    wrTop Q n ⟨WreathMod.wr q f, WreathMod.wr_mem q f⟩ = q := by
  simp [wrTop]

lemma wrTop_comp_wrHom {Q : Type} [Group Q] {n : ℕ} (φ : FreeGroup α →* Q)
    (f : α → Q → ZMod n) : (wrTop Q n).comp (wrHom φ f) = φ :=
  FreeGroup.ext_hom _ _ fun i ↦ by simp [wrHom, wrTop]

open Classical in
lemma cnt_one_mul {Q : Type} [Group Q] [Finite Q] {n : ℕ} (s : Q) (q : ℕ) :
    (cnt s 1 (orderOf s * q) : ZMod n) = q := by
  have : (Finset.range (orderOf s * q)).filter (fun i ↦ s ^ i * 1 = 1) =
      (Finset.range (orderOf s * q)).filter (orderOf s ∣ ·) := by
    ext i
    simp [orderOf_dvd_iff_pow_eq_one]
  rw [cnt, this, card_filter_dvd_range_mul _ _ (orderOf_pos s)]

open Classical in
lemma exists_of_cnt_ne_zero {Q : Type} [Group Q] {n : ℕ} {s y : Q} {k : ℕ}
    (h : (cnt s y k : ZMod n) ≠ 0) : ∃ i < k, s ^ i * y = 1 := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have : (Finset.range k).filter (fun i ↦ s ^ i * y = 1) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun i hi ↦ hne i (Finset.mem_range.1 hi)
  rw [cnt, this, Finset.card_empty, Nat.cast_zero] at h
  exact h rfl

/-- A non-trivial element of `inertiaSigma P a` is detected by a character `χ_N`. -/
lemma exists_chi_ne_one [DecidableEq α] {a : α} {z : ProSigmaCompletion P (FreeGroup α)}
    (hz : z ∈ inertiaSigma P (FreeGroup.of a)) (hz1 : z ≠ 1) :
    ∃ (N : ℕ) (_ : NeZero N) (hN : IsSigmaNat P N),
      liftFinite (chi a N) (isSigmaNat_card_chi hN) z ≠ 1 := by
  by_contra h
  push Not at h
  exact hz1 (eq_one_of_mem_of_chi hz fun N inst hN ↦ h N inst hN)

/-- **The centraliser of a non-trivial element of `inertiaSigma P a` lies in
`inertiaSigma P a`.** -/
theorem mem_inertiaSigma_of_commute {a : α}
    {z w : ProSigmaCompletion P (FreeGroup α)} (hz : z ∈ inertiaSigma P (FreeGroup.of a))
    (hz1 : z ≠ 1) (hw : w * z = z * w) : w ∈ inertiaSigma P (FreeGroup.of a) := by
  classical
  by_contra hwA
  obtain ⟨Q₀, _, _, f₀, hQ₀, hf₀⟩ : ∃ (Q₀ : Type) (_ : Group Q₀) (_ : Finite Q₀)
      (f₀ : FreeGroup α →* Q₀) (hQ₀ : IsSigmaNat P (Nat.card Q₀)),
      liftFinite f₀ hQ₀ w ∉ Subgroup.zpowers (f₀ (FreeGroup.of a)) := by
    by_contra h
    push Not at h
    exact hwA (mem_inertiaSigma_of fun Q _ _ f hQ ↦ h Q _ _ f hQ)
  -- a character `χ_N` with `χ_N(z) ≠ 1`, and a prime `ℓ ∣ N` (so `ℓ ∈ Σ`)
  obtain ⟨N, _, hN, hχ⟩ := exists_chi_ne_one hz hz1
  obtain ⟨i₀, hi₀⟩ := exists_liftFinite_eq_pow (chi a N) (isSigmaNat_card_chi hN) hz
  have hNi₀ : ¬ N ∣ i₀ := by
    intro h
    apply hχ
    rw [hi₀, ← orderOf_dvd_iff_pow_eq_one, orderOf_chi_of_self]
    exact h
  obtain ⟨ℓ, hℓ, hℓi₀⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ^ N.factorization ℓ ∣ i₀ := by
    by_contra h
    push Not at h
    apply hNi₀
    rcases Nat.eq_zero_or_pos i₀ with h0 | hi
    · rw [h0]
      exact dvd_zero _
    rw [← Nat.factorization_le_iff_dvd hN.1 hi.ne']
    intro p
    by_cases hp : p.Prime
    · exact (hp.pow_dvd_iff_le_factorization hi.ne').1 (h p hp)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  set k := N.factorization ℓ with hk
  have hk0 : k ≠ 0 := by
    intro h
    apply hℓi₀
    rw [h, pow_zero]
    exact one_dvd _
  have hPℓ : P ℓ := hN.2 ℓ hℓ (Nat.dvd_of_factorization_pos hk0)
  have hℓkN : ℓ ^ k ∣ N := Nat.ordProj_dvd N ℓ
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  -- the finite quotient `φ = f₀ × χ_N` and the wreath homomorphism `ψ : F → (ℤ/ℓ) ≀ Q`
  set Q := Q₀ × ULift.{0} (Multiplicative (ZMod N))
  have hQ : IsSigmaNat P (Nat.card Q) := by
    rw [Nat.card_prod]
    exact hQ₀.mul (isSigmaNat_card_chi hN)
  set φ : FreeGroup α →* Q := f₀.prod (chi a N) with hφ
  set s := φ (FreeGroup.of a) with hs
  set o := orderOf s with ho
  have hNo : N ∣ o := by
    rw [← orderOf_chi_of_self a N]
    refine orderOf_dvd_of_pow_eq_one ?_
    have := congrArg Prod.snd (pow_orderOf_eq_one s)
    rw [Prod.pow_snd] at this
    exact this
  set fδ : α → Q → ZMod ℓ := fun b ↦ if b = a then delta else 0
  set ψ := wrHom φ fδ
  have hW := isSigmaNat_card_wrSub (n := ℓ) hQ hℓ hPℓ
  have htop : ∀ x, wrTop Q ℓ (liftFinite ψ hW x) = liftFinite φ hQ x := fun x ↦ by
    rw [← liftFinite_comp ψ (wrTop Q ℓ) hW hQ, wrTop_comp_wrHom]
  obtain ⟨i, hi⟩ := exists_liftFinite_eq_pow ψ hW hz
  have hφz : liftFinite φ hQ z = s ^ i := by
    rw [← htop, hi, map_pow, ← MonoidHom.comp_apply, wrTop_comp_wrHom]
  have hχz : liftFinite (chi a N) (isSigmaNat_card_chi hN) z = chi a N (FreeGroup.of a) ^ i := by
    have := liftFinite_comp φ (MonoidHom.snd _ _) hQ (isSigmaNat_card_chi hN) z
    rw [MonoidHom.snd_comp_prod] at this
    rw [this, hφz, map_pow]
    rfl
  have hmod : i ≡ i₀ [MOD N] := by
    rw [← orderOf_chi_of_self a N, ← pow_eq_pow_iff_modEq, ← hχz, hi₀]
  have hℓi : ¬ ℓ ^ k ∣ i := fun h ↦ hℓi₀ ((hmod.dvd_iff hℓkN).1 h)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hℓi (dvd_zero _)
  -- `i = ℓ ^ t * i'` with `t < k` and `ℓ ∤ i'`
  set t := i.factorization ℓ
  have ht : t < k := by
    by_contra h
    push Not at h
    exact hℓi ((pow_dvd_pow ℓ h).trans (Nat.ordProj_dvd i ℓ))
  set i' := i / ℓ ^ t
  have hi' : ℓ ^ t * i' = i := Nat.ordProj_mul_ordCompl_eq_self i ℓ
  have hℓi' : ¬ ℓ ∣ i' := Nat.not_dvd_ordCompl hℓ hi0
  obtain ⟨M, hM⟩ : ℓ ^ t ∣ o := (pow_dvd_pow ℓ ht.le).trans (hℓkN.trans hNo)
  -- `z ^ M` lies in the kernel of `φ̂`, and `ψ̂(z ^ M) = wr 1 (i' · 1_{⟨s⟩})`
  have hψa : (ψ (FreeGroup.of a) : Equiv.Perm (Q × ZMod ℓ)) = wr s delta := by
    simp [ψ, wrHom_of, fδ, s]
  have hK : (liftFinite ψ hW (z ^ M) : Equiv.Perm (Q × ZMod ℓ)) =
      wr 1 (fun y ↦ cnt s y (o * i')) := by
    rw [map_pow, hi, ← pow_mul, show i * M = o * i' by rw [← hi', hM]; ring, Subgroup.coe_pow,
      hψa, wr_pow, pow_mul, show s ^ o = 1 from pow_orderOf_eq_one s, one_pow]
    congr 1
    funext y
    exact sum_delta s y _
  obtain ⟨q, e, he⟩ := (liftFinite ψ hW w).2
  have hq : q = liftFinite φ hQ w := by
    rw [← htop w, ← wrTop_wr (n := ℓ) q e]
    congr 1
    exact Subtype.ext he
  have hc : liftFinite ψ hW (w * z ^ M) = liftFinite ψ hW (z ^ M * w) := by
    rw [((Commute.pow_right hw M)).eq]
  have hc' := congrArg Subtype.val hc
  simp only [map_mul, Subgroup.coe_mul] at hc'
  rw [hK, ← he] at hc'
  have hinv := invariant_of_commute hc' 1
  rw [mul_one, show (cnt s 1 (o * i') : ZMod ℓ) = i' from cnt_one_mul s i'] at hinv
  have hne : (cnt s q (o * i') : ZMod ℓ) ≠ 0 := by
    rw [hinv, Ne, ZMod.natCast_eq_zero_iff]
    exact hℓi'
  obtain ⟨j, -, hj⟩ := exists_of_cnt_ne_zero hne
  apply hf₀
  have hq' : liftFinite φ hQ w = (s ^ j)⁻¹ := hq ▸ eq_inv_of_mul_eq_one_right hj
  have hfst := liftFinite_comp φ (MonoidHom.fst _ _) hQ hQ₀ w
  rw [MonoidHom.fst_comp_prod, hq'] at hfst
  rw [hfst]
  simp only [s, φ]
  exact inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)

/-- **Inertia groups of basis elements are malnormal.** -/
theorem inertiaSigma_inf_conj_eq_bot_self {a : α} {σ : ProSigmaCompletion P (FreeGroup α)}
    (hσ : σ ∉ inertiaSigma P (FreeGroup.of a)) :
    inertiaSigma P (FreeGroup.of a) ⊓
      (ConjAct.toConjAct σ • inertiaSigma P (FreeGroup.of a)) = ⊥ := by
  classical
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ ?_
  obtain ⟨hza, hzb⟩ := Subgroup.mem_inf.1 hz
  rw [mem_toConjAct_smul_iff] at hzb
  have h := conj_eq_of_mem hza hzb
  by_contra hz1
  refine hσ (mem_inertiaSigma_of_commute hza hz1 ?_)
  calc σ * z = σ * (σ⁻¹ * z * σ) := by rw [h]
    _ = z * σ := by group

end Centraliser

/-! ### Injectivity of `ℤ^Σ → F^Σ`, `1 ↦ a` -/

section Injective

variable {α : Type}

/-- **`ℤ^Σ → F(α)^Σ`, `1 ↦ a`, is injective** for a basis element `a`. -/
theorem map_zpowersHom_of_injective (a : α) :
    Function.Injective (map (P := P) (zpowersHom (FreeGroup α) (FreeGroup.of a))) := by
  classical
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ eq_one_of_forall_liftFinite fun Q _ _ f hQ ↦ ?_
  set o := orderOf (f (Multiplicative.ofAdd 1))
  have ho : IsSigmaNat P o := hQ.of_dvd (orderOf_dvd_natCard _)
  haveI : NeZero o := ⟨ho.1⟩
  set χ' := (chi a o).comp (zpowersHom _ (FreeGroup.of a))
  have hχ' : liftFinite χ' (isSigmaNat_card_chi ho) x = 1 := by
    rw [← liftFinite_map, hx, map_one]
  obtain ⟨w, hw1, hw2⟩ := exists_eta_mem_of_isOpen
    ((isOpen_liftFinite_fiber f hQ (liftFinite f hQ x)).inter
      (isOpen_liftFinite_fiber χ' (isSigmaNat_card_chi ho) 1)) ⟨rfl, hχ'⟩
  have hw1' : f w = liftFinite f hQ x := by rw [← liftFinite_eta]; exact hw1
  have hw2' : χ' w = 1 := by rw [← liftFinite_eta (P := P) χ' (isSigmaNat_card_chi ho)]; exact hw2
  rw [← hw1']
  have hw : w = Multiplicative.ofAdd 1 ^ Multiplicative.toAdd w := by
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  simp only [χ', MonoidHom.comp_apply, zpowersHom_apply, map_zpow] at hw2'
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_chi_of_self] at hw2'
  rw [hw, map_zpow]
  exact orderOf_dvd_iff_zpow_eq_one.1 hw2'

theorem map_zpowersHom_injective_mulEquiv (e : Γ ≃* Γ') {γ : Γ}
    (h : Function.Injective (map (P := P) (zpowersHom Γ γ))) :
    Function.Injective (map (P := P) (zpowersHom Γ' (e γ))) := by
  have h' : zpowersHom Γ' (e γ) = e.toMonoidHom.comp (zpowersHom Γ γ) := by
    ext
    simp
  rw [h', ← map_comp]
  exact (congr (P := P) e).injective.comp h

end Injective

end ProSigmaCompletion

end Profinite

namespace SurfaceGroup

open Profinite Profinite.ProSigmaCompletion

variable {P : ℕ → Prop} {g : ℕ}

theorem range_cuspInertiaSigma {r : ℕ} (j : Fin r) :
    (cuspInertiaSigma P (g := g) j).range = inertiaSigma P (cusp j) := rfl

/-- The inertia groups of the cusps `c_j`, `j < r`, of `Π^Σ_{g,r+1}` are the images of the
inertia groups of basis elements of `F(a, b, c_{<r})^Σ`. -/
theorem inertiaSigma_cusp_castSucc {r : ℕ} (j : Fin r) :
    inertiaSigma P (cusp (g := g) j.castSucc) =
      (inertiaSigma P (FreeGroup.of (SurfaceGen.c j))).map
        (ProSigmaCompletion.congr (P := P)
          (freeEquiv (g := g) (r := r)).symm).toMulEquiv.toMonoidHom := by
  rw [← inertiaSigma_mulEquiv]
  congr 1

/-- Moving cusps by an automorphism, up to conjugacy. -/
theorem exists_inertiaSigma_cusp_eq {r : ℕ} (π : Equiv.Perm (Fin r)) :
    ∃ (E : proSigma P g r ≃* proSigma P g r) (c : Fin r → proSigma P g r), ∀ k,
      inertiaSigma P (cusp (g := g) k) =
        (ConjAct.toConjAct (c k) • inertiaSigma P (cusp (π k))).map E.toMonoidHom ∧
      cuspInertiaSigma P k = E.toMonoidHom.comp ((MulAut.conj (c k)).toMonoidHom.comp
        (cuspInertiaSigma P (π k))) := by
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_isConj_cusp (g := g) π
  choose c hc using fun k ↦ isConj_iff.1 (hθ k)
  refine ⟨(ProSigmaCompletion.congr (P := P) θ.symm).toMulEquiv, fun k ↦ eta P (c k)⁻¹,
    fun k ↦ ⟨?_, ?_⟩⟩
  · have : cusp k = θ.symm ((c k)⁻¹ * cusp (π k) * (c k)⁻¹⁻¹) := by
      rw [MulEquiv.eq_symm_apply, ← hc k]
      group
    rw [this, inertiaSigma_mulEquiv, inertiaSigma_conj]
  · have h1 : zpowersHom _ (cusp (g := g) k) = θ.symm.toMonoidHom.comp
        ((MulAut.conj (c k)⁻¹).toMonoidHom.comp (zpowersHom _ (cusp (π k)))) := by
      ext
      simp only [zpowersHom_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply, MulAut.conj_apply, toAdd_ofAdd, zpow_one]
      rw [MulEquiv.eq_symm_apply, ← hc k]
      group
    have hcont : Continuous (MulAut.conj (eta P (c k)⁻¹)).toMonoidHom := by
      change Continuous fun y ↦ eta P (c k)⁻¹ * y * (eta P (c k)⁻¹)⁻¹
      fun_prop
    have h2 : ProSigmaCompletion.map (P := P) (MulAut.conj (c k)⁻¹).toMonoidHom =
        (MulAut.conj (eta P (c k)⁻¹)).toMonoidHom :=
      ProSigmaCompletion.hom_ext (continuous_map _) hcont fun x ↦ by simp [map_eta]
    rw [cuspInertiaSigma, h1, ← ProSigmaCompletion.map_comp, ← ProSigmaCompletion.map_comp, h2]
    rfl

/-- **Distinct cusp inertia groups of `Π^Σ_{g,r}` (`r ≥ 3`) meet trivially, also after
conjugation**: `I_i ∩ σ I_j σ⁻¹ = 1` for `i ≠ j`. -/
theorem cuspInertiaSigma_inf_conj_eq_bot {r : ℕ} {i j : Fin (r + 3)} (hij : i ≠ j)
    (σ : proSigma P g (r + 3)) :
    (cuspInertiaSigma P (g := g) i).range ⊓
      (ConjAct.toConjAct σ • (cuspInertiaSigma P (g := g) j).range) = ⊥ := by
  -- a permutation sending `i ↦ 0`, `j ↦ 1`
  set π : Equiv.Perm (Fin (r + 3)) := Equiv.swap (Equiv.swap i 0 j) 1 * Equiv.swap i 0
  have hj0 : Equiv.swap i 0 j ≠ 0 := by
    intro h
    exact hij ((Equiv.swap_apply_eq_iff.1 h).trans (Equiv.swap_apply_right i 0)).symm
  have hπi : π i = 0 := by
    simp only [π, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hj0.symm (by simp)
  have hπj : π j = 1 := by
    simp only [π, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  obtain ⟨E, c, hc⟩ := exists_inertiaSigma_cusp_eq (P := P) (g := g) π
  rw [range_cuspInertiaSigma, range_cuspInertiaSigma, (hc i).1, (hc j).1, hπi, hπj]
  refine inf_conj_eq_bot_map E (fun τ ↦ inf_conj_eq_bot_conj ?_ (c i) (c j) τ) σ
  intro τ
  have h0 : (0 : Fin (r + 3)) = (0 : Fin (r + 2)).castSucc := rfl
  have h1 : (1 : Fin (r + 3)) = (1 : Fin (r + 2)).castSucc := by simp
  rw [h0, h1, inertiaSigma_cusp_castSucc, inertiaSigma_cusp_castSucc]
  exact inf_conj_eq_bot_map _ (inertiaSigma_inf_conj_eq_bot_of_ne (by simp)) τ

/-- **Cusp inertia groups of `Π^Σ_{g,r}` (`r ≥ 2`) are malnormal**: `I_k ∩ σ I_k σ⁻¹ = 1` for
`σ ∉ I_k`. -/
theorem cuspInertiaSigma_inf_conj_eq_bot_self {r : ℕ} (k : Fin (r + 2))
    {σ : proSigma P g (r + 2)} (hσ : σ ∉ (cuspInertiaSigma P (g := g) k).range) :
    (cuspInertiaSigma P (g := g) k).range ⊓
      (ConjAct.toConjAct σ • (cuspInertiaSigma P (g := g) k).range) = ⊥ := by
  obtain ⟨E, c, hc⟩ := exists_inertiaSigma_cusp_eq (P := P) (g := g) (Equiv.swap k 0)
  rw [range_cuspInertiaSigma, (hc k).1, Equiv.swap_apply_left] at hσ ⊢
  refine inf_conj_self_eq_bot_map E (fun τ hτ ↦ inf_conj_self_eq_bot_conj ?_ (c k) τ hτ) σ hσ
  intro τ hτ
  have h0 : (0 : Fin (r + 2)) = (0 : Fin (r + 1)).castSucc := rfl
  rw [h0, inertiaSigma_cusp_castSucc] at hτ ⊢
  exact inf_conj_self_eq_bot_map _ (fun _ ↦ inertiaSigma_inf_conj_eq_bot_self) τ hτ

/-- **The cusp inertia `ℤ^Σ → Π^Σ_{g,r}` is injective** (`r ≥ 2`). -/
theorem cuspInertiaSigma_injective {r : ℕ} (k : Fin (r + 2)) :
    Function.Injective (cuspInertiaSigma P (g := g) k) := by
  obtain ⟨E, c, hc⟩ := exists_inertiaSigma_cusp_eq (P := P) (g := g) (Equiv.swap k 0)
  rw [(hc k).2, Equiv.swap_apply_left]
  refine E.injective.comp ((MulAut.conj (c k)).injective.comp ?_)
  have h0 : (0 : Fin (r + 2)) = (0 : Fin (r + 1)).castSucc := rfl
  rw [h0, cuspInertiaSigma]
  have h := map_zpowersHom_injective_mulEquiv (P := P) (freeEquiv (g := g) (r := r + 1)).symm
    (map_zpowersHom_of_injective (SurfaceGen.c (0 : Fin (r + 1))))
  have hc0 : (freeEquiv (g := g) (r := r + 1)).symm (FreeGroup.of (SurfaceGen.c 0)) =
      cusp (Fin.castSucc 0) := by
    rw [MulEquiv.symm_apply_eq, freeEquiv_cusp_castSucc]
  rwa [hc0] at h

/-- **Estrangedness at a vertex of type `(0, 3)`** ([SemiAnbd] Def 2.4(iv), Ex 2.10): in
`Π^Σ_{0,3}`, conjugates of the inertia groups of distinct cusps meet trivially, and the cusp
inertia groups are malnormal. -/
theorem cuspInertiaSigma_estranged_zero_three :
    (∀ (i j : Fin 3), i ≠ j → ∀ σ : proSigma P 0 3,
      (cuspInertiaSigma P (g := 0) i).range ⊓
        (ConjAct.toConjAct σ • (cuspInertiaSigma P (g := 0) j).range) = ⊥) ∧
    (∀ (k : Fin 3) (σ : proSigma P 0 3), σ ∉ (cuspInertiaSigma P (g := 0) k).range →
      (cuspInertiaSigma P (g := 0) k).range ⊓
        (ConjAct.toConjAct σ • (cuspInertiaSigma P (g := 0) k).range) = ⊥) :=
  ⟨fun _ _ hij σ ↦ cuspInertiaSigma_inf_conj_eq_bot (r := 0) hij σ,
    fun k _ hσ ↦ cuspInertiaSigma_inf_conj_eq_bot_self (r := 1) k hσ⟩

end SurfaceGroup

end Pi1
