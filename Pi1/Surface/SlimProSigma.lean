/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.ProSigma
public import Pi1.Profinite.Slim
public import Mathlib.Data.ZMod.Basic

/-!
# Slimness of pro-`Σ` free groups and pro-`Σ` surface groups

Let `Σ` be a set of primes (a predicate `P`) containing a prime `ℓ`. We prove that the pro-`Σ`
completion of a free group on a type with at least two elements is **slim** (every open subgroup
has trivial centraliser; `Pi1.Profinite.ProSigmaCompletion.isSlim_freeGroup`), and deduce that the
pro-`Σ` surface group `Π^Σ_{g,r}` is slim for hyperbolic `(g, r)` with `r ≥ 1`
(`Pi1.SurfaceGroup.isSlim_proSigma`), in particular centre-free. This is the slimness of the
vertex groups required in [SemiAnbd] Def 2.4(ii) ("vertically slim") for the pro-`Σ` semi-graph
of anabelioids `G^Σ` of a stable curve.

* `ProSigmaCompletion.map_comp`, `map_id`, **`ProSigmaCompletion.congr`**: functoriality of the
  pro-`Σ` completion; a group isomorphism `Γ ≃* Γ'` induces `Γ^Σ ≃ₜ* Γ'^Σ`.
* `WreathMod`: the wreath product `(ℤ/n)^Q ⋊ Q` as the subgroup `WreathMod.wrSub` of
  `Perm (Q × ℤ/n)`, of order `n ^ |Q| · |Q|` (`WreathMod.card_wrSub`).

## The argument

The proof follows `Pi1.Profinite.isSlim_completion_freeGroup`, with `𝔽₂` replaced by `𝔽_ℓ`.
Suppose `z ≠ 1` in `F^Σ` centralises an open subgroup `U`. Choose an open normal `M ⊆ U` with
`z ∉ M`; then `Q = F^Σ / M` is finite of `Σ`-integer order (`F^Σ` is pro-`Σ`). For
`f : α → (Q → 𝔽_ℓ)` the homomorphism `ψ_f : F → 𝔽_ℓ ≀ Q`, `x ↦ wr (φ x) (f x)`, lands in the
finite wreath product of order `ℓ ^ |Q| · |Q|`, a `Σ`-integer, so it extends to `F^Σ`
(`ProSigmaCompletion.liftFinite`). The rest of the argument (indicator cocycles of `⟨φ a⟩`,
`⟨φ b⟩`) is unchanged, since a count `≤ 1` is detected modulo `ℓ`.
-/

@[expose] public section

open Topology

universe u

namespace Pi1.Profinite

/-! ### Functoriality of the pro-`Σ` completion -/

namespace ProSigmaCompletion

variable {P : ℕ → Prop} {Γ Γ' Γ'' : Type u} [Group Γ] [Group Γ'] [Group Γ'']

/-- Two continuous homomorphisms out of `Γ^Σ` that agree on the image of `Γ` are equal. -/
theorem hom_ext {φ ψ : ProSigmaCompletion P Γ →* ProSigmaCompletion P Γ'} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : ∀ x : Γ, φ (eta P x) = ψ (eta P x)) : φ = ψ :=
  DFunLike.coe_injective <| (denseRange_eta (P := P) (Γ := Γ)).equalizer hφ hψ (funext h)

theorem map_comp (φ : Γ →* Γ') (ψ : Γ' →* Γ'') :
    (map (P := P) ψ).comp (map φ) = map (ψ.comp φ) :=
  hom_ext ((continuous_map ψ).comp (continuous_map φ)) (continuous_map _) fun x ↦ by
    simp

theorem map_id : map (P := P) (MonoidHom.id Γ) = MonoidHom.id _ :=
  hom_ext (continuous_map _) continuous_id fun x ↦ by simp

/-- **A group isomorphism induces an isomorphism of pro-`Σ` completions.** -/
noncomputable def congr (e : Γ ≃* Γ') : ProSigmaCompletion P Γ ≃ₜ* ProSigmaCompletion P Γ' where
  toFun := map e.toMonoidHom
  invFun := map e.symm.toMonoidHom
  left_inv x := by
    change ((map (P := P) e.symm.toMonoidHom).comp (map e.toMonoidHom)) x = x
    rw [map_comp]
    simp [map_id]
  right_inv x := by
    change ((map (P := P) e.toMonoidHom).comp (map e.symm.toMonoidHom)) x = x
    rw [map_comp]
    simp [map_id]
  map_mul' := map_mul _
  continuous_toFun := continuous_map _
  continuous_invFun := continuous_map _

@[simp]
theorem congr_eta (e : Γ ≃* Γ') (x : Γ) : congr (P := P) e (eta P x) = eta P (e x) :=
  map_eta _ x

end ProSigmaCompletion

/-! ### The wreath product `(ℤ/n) ≀ Q` as a finite group -/

namespace WreathMod

variable {Q : Type u} [Group Q] {n : ℕ}

/-- The permutation `(y, c) ↦ (q y, c + f y)` of `Q × ℤ/n`. -/
def wr (q : Q) (f : Q → ZMod n) : Equiv.Perm (Q × ZMod n) where
  toFun p := (q * p.1, p.2 + f p.1)
  invFun p := (q⁻¹ * p.1, p.2 - f (q⁻¹ * p.1))
  left_inv p := by simp
  right_inv p := by simp

@[simp]
lemma wr_apply (q : Q) (f : Q → ZMod n) (p : Q × ZMod n) : wr q f p = (q * p.1, p.2 + f p.1) :=
  rfl

lemma wr_mul (q q' : Q) (f f' : Q → ZMod n) :
    wr q f * wr q' f' = wr (q * q') (fun x ↦ f' x + f (q' * x)) := by
  ext p
  · simp [mul_assoc]
  · simp [add_assoc]

lemma wr_injective {q q' : Q} {f f' : Q → ZMod n} (h : wr q f = wr q' f') : q = q' ∧ f = f' := by
  refine ⟨?_, funext fun x ↦ ?_⟩
  · simpa using congrArg Prod.fst (Equiv.ext_iff.1 h (1, 0))
  · simpa using congrArg Prod.snd (Equiv.ext_iff.1 h (x, 0))

lemma wr_one_zero : wr (1 : Q) (0 : Q → ZMod n) = 1 := by
  ext p <;> simp

lemma wr_inv (q : Q) (f : Q → ZMod n) : (wr q f)⁻¹ = wr q⁻¹ (fun x ↦ -f (q⁻¹ * x)) := by
  rw [inv_eq_iff_mul_eq_one, wr_mul, ← wr_one_zero]
  congr 1
  · simp
  · funext x
    simp

lemma wr_pow (q : Q) (f : Q → ZMod n) (k : ℕ) :
    wr q f ^ k = wr (q ^ k) (fun x ↦ ∑ i ∈ Finset.range k, f (q ^ i * x)) := by
  induction k with
  | zero =>
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty]
    exact wr_one_zero.symm
  | succ k ih =>
    rw [pow_succ, ih, wr_mul, pow_succ]
    congr 1
    funext x
    rw [Finset.sum_range_succ', pow_zero, one_mul, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pow_succ, mul_assoc]

/-- If `wr z e` commutes with `wr 1 d`, then `d` is invariant under left translation by `z`. -/
lemma invariant_of_commute {z : Q} {e d : Q → ZMod n} (h : wr z e * wr 1 d = wr 1 d * wr z e)
    (x : Q) : d (z * x) = d x := by
  rw [wr_mul, wr_mul] at h
  have := congrFun (wr_injective h).2 x
  simp only [one_mul] at this
  rw [add_comm] at this
  exact (add_left_cancel this).symm

variable (Q n) in
/-- **The wreath product** `(ℤ/n)^Q ⋊ Q`: the subgroup of `Perm (Q × ℤ/n)` of all `wr q f`. -/
def wrSub : Subgroup (Equiv.Perm (Q × ZMod n)) where
  carrier := {σ | ∃ q f, wr q f = σ}
  mul_mem' := by
    rintro _ _ ⟨q, f, rfl⟩ ⟨q', f', rfl⟩
    exact ⟨_, _, (wr_mul q q' f f').symm⟩
  one_mem' := ⟨1, 0, wr_one_zero⟩
  inv_mem' := by
    rintro _ ⟨q, f, rfl⟩
    exact ⟨_, _, (wr_inv q f).symm⟩

lemma wr_mem (q : Q) (f : Q → ZMod n) : wr q f ∈ wrSub Q n := ⟨q, f, rfl⟩

/-- `|(ℤ/n) ≀ Q| = n ^ |Q| · |Q|`. -/
lemma card_wrSub [Finite Q] [NeZero n] : Nat.card (wrSub Q n) = n ^ Nat.card Q * Nat.card Q := by
  have hb : Function.Bijective (fun p : (Q → ZMod n) × Q ↦
      (⟨wr p.2 p.1, wr_mem p.2 p.1⟩ : wrSub Q n)) := by
    refine ⟨fun p p' h ↦ ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := wr_injective (congrArg Subtype.val h)
      exact Prod.ext h2 h1
    · rintro ⟨_, q, f, rfl⟩
      exact ⟨(f, q), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_prod, Nat.card_fun, Nat.card_zmod]

instance [Finite Q] [NeZero n] : Finite (wrSub Q n) :=
  Nat.finite_of_card_ne_zero <| by
    rw [card_wrSub]
    exact mul_ne_zero (pow_ne_zero _ (NeZero.ne n)) Nat.card_pos.ne'

/-- For `ℓ ∈ Σ` prime and `|Q|` a `Σ`-integer, `|(ℤ/ℓ) ≀ Q|` is a `Σ`-integer. -/
lemma isSigmaNat_card_wrSub {P : ℕ → Prop} [Finite Q] (hQ : IsSigmaNat P (Nat.card Q))
    (hn : n.Prime) (hP : P n) : IsSigmaNat P (Nat.card (wrSub Q n)) := by
  haveI : NeZero n := ⟨hn.ne_zero⟩
  rw [card_wrSub]
  refine IsSigmaNat.mul ⟨pow_ne_zero _ hn.ne_zero, fun p hp h ↦ ?_⟩ hQ
  rw [(Nat.prime_dvd_prime_iff_eq hp hn).1 (hp.dvd_of_dvd_pow h)]
  exact hP

section Count

open Classical in
/-- The indicator of `1 : Q`. -/
noncomputable def delta : Q → ZMod n := fun x ↦ if x = 1 then 1 else 0

open Classical in
/-- The number of `i < k` with `s ^ i * y = 1`, modulo `n`. -/
noncomputable def cnt (s y : Q) (k : ℕ) : ZMod n :=
  ((Finset.range k).filter fun i ↦ s ^ i * y = 1).card

lemma sum_delta (s y : Q) (k : ℕ) :
    ∑ i ∈ Finset.range k, (delta (s ^ i * y) : ZMod n) = cnt s y k := by
  classical
  simp only [delta, cnt]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

open Classical in
lemma exists_of_cnt_eq_one [Nontrivial (ZMod n)] {s y : Q} {k : ℕ} (h : (cnt s y k : ZMod n) = 1) :
    ∃ i < k, s ^ i * y = 1 := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have : (Finset.range k).filter (fun i ↦ s ^ i * y = 1) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun i hi ↦ hne i (Finset.mem_range.1 hi)
  rw [cnt, this, Finset.card_empty, Nat.cast_zero] at h
  exact zero_ne_one h

open Classical in
lemma cnt_one {s : Q} {k : ℕ} (hk : 0 < k) (hs : k ≤ orderOf s) : (cnt s 1 k : ZMod n) = 1 := by
  have : (Finset.range k).filter (fun i ↦ s ^ i * 1 = 1) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, mul_one, Finset.mem_singleton]
    constructor
    · rintro ⟨hi, h⟩
      by_contra h0
      exact pow_ne_one_of_lt_orderOf h0 (lt_of_lt_of_le hi hs) h
    · rintro rfl
      exact ⟨hk, pow_zero s⟩
  rw [cnt, this, Finset.card_singleton, Nat.cast_one]

end Count

end WreathMod

open WreathMod

/-! ### The main argument -/

namespace ProSigmaCompletion

variable {P : ℕ → Prop} {α : Type u}

/-- The homomorphism `F(α) → (ℤ/n) ≀ Q`, `x ↦ wr (φ x) (f x)`. -/
noncomputable def wrHom {Q : Type u} [Group Q] {n : ℕ} (φ : FreeGroup α →* Q)
    (f : α → Q → ZMod n) : FreeGroup α →* wrSub Q n :=
  FreeGroup.lift fun i ↦ ⟨wr (φ (FreeGroup.of i)) (f i), wr_mem _ _⟩

lemma wrHom_eq {Q : Type u} [Group Q] {n : ℕ} (φ : FreeGroup α →* Q) (f : α → Q → ZMod n)
    (w : FreeGroup α) : ∃ d, (wrHom φ f w : Equiv.Perm (Q × ZMod n)) = wr (φ w) d := by
  induction w using FreeGroup.induction_on with
  | C1 => exact ⟨0, by simp [wr_one_zero]⟩
  | of i => exact ⟨f i, by simp [wrHom]⟩
  | inv_of i _ =>
    exact ⟨fun x ↦ -f i ((φ (FreeGroup.of i))⁻¹ * x), by simp [wrHom, wr_inv]⟩
  | mul x y hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨_, by rw [map_mul, Subgroup.coe_mul, hd, hd', wr_mul, map_mul]⟩

lemma wrHom_of {Q : Type u} [Group Q] {n : ℕ} (φ : FreeGroup α →* Q) (f : α → Q → ZMod n)
    (i : α) : (wrHom φ f (FreeGroup.of i) : Equiv.Perm (Q × ZMod n)) =
      wr (φ (FreeGroup.of i)) (f i) := by
  simp [wrHom]

variable (P) in
/-- **Invariance of cocycles under a centralising element**, pro-`Σ` form. Let `M` be an open
normal subgroup of `F(α)^Σ` with quotient `Q` of `Σ`-integer order, `ℓ ∈ Σ` prime,
`φ : F(α) → Q`, and let `z` commute with the image of every element of `ker φ`. Then for every
`f` and `k ∈ ker φ`, writing `wrHom φ f k = wr 1 d`, the function `d` is invariant under
translation by the image of `z`. -/
lemma invariant_of_ker {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ)
    (M : Subgroup (ProSigmaCompletion P (FreeGroup α))) [M.Normal]
    (hM : IsOpen (M : Set (ProSigmaCompletion P (FreeGroup α))))
    [Finite (ProSigmaCompletion P (FreeGroup α) ⧸ M)]
    (hQ : IsSigmaNat P (Nat.card (ProSigmaCompletion P (FreeGroup α) ⧸ M)))
    (z : ProSigmaCompletion P (FreeGroup α))
    (hz : ∀ k : FreeGroup α,
      (QuotientGroup.mk (eta P k) : ProSigmaCompletion P (FreeGroup α) ⧸ M) = 1 →
      z * eta P k = eta P k * z)
    (f : α → (ProSigmaCompletion P (FreeGroup α) ⧸ M) → ZMod ℓ) (k : FreeGroup α)
    {d : (ProSigmaCompletion P (FreeGroup α) ⧸ M) → ZMod ℓ}
    (hk : (wrHom ((QuotientGroup.mk' M).comp (eta P)) f k : Equiv.Perm _) = wr 1 d)
    (hk1 : (QuotientGroup.mk (eta P k) : ProSigmaCompletion P (FreeGroup α) ⧸ M) = 1)
    (x : ProSigmaCompletion P (FreeGroup α) ⧸ M) :
    d (QuotientGroup.mk z * x) = d x := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hW := isSigmaNat_card_wrSub (n := ℓ) hQ hℓ hP
  let ψ := wrHom ((QuotientGroup.mk' M).comp (eta P)) f
  obtain ⟨x₀, hx₀, hψ⟩ := exists_eta_mem_of_isOpen ((isOpen_setOf_mk_eq M hM z).inter
    (isOpen_liftFinite_fiber ψ hW (liftFinite ψ hW z))) ⟨rfl, rfl⟩
  obtain ⟨e, he⟩ := wrHom_eq ((QuotientGroup.mk' M).comp (eta P)) f x₀
  have hφ : ((QuotientGroup.mk' M).comp (eta P)) x₀ = QuotientGroup.mk z := hx₀
  have hz' : ((liftFinite ψ hW z).1 : Equiv.Perm _) = wr (QuotientGroup.mk z) e := by
    rw [← hψ, liftFinite_eta, he, hφ]
  have hc := congrArg (fun w ↦ (liftFinite ψ hW w).1) (hz k hk1)
  simp only [map_mul, Subgroup.coe_mul, liftFinite_eta, ψ] at hc
  rw [hk, hz'] at hc
  exact invariant_of_commute hc x

/-- **The pro-`Σ` completion of a free group of rank `≥ 2` is slim**, for every set of primes `Σ`
containing a prime `ℓ`. -/
theorem isSlim_freeGroup {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) {a b : α} (hab : a ≠ b) :
    IsSlim (ProSigmaCompletion P (FreeGroup α)) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  intro U z hz
  by_contra hz1
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one U.isOpen
    U.one_mem
  obtain ⟨N', hN'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := z)) (by simpa [eq_comm] using hz1)
  set M : Subgroup (ProSigmaCompletion P (FreeGroup α)) := N.toSubgroup ⊓ N'.toSubgroup
  have hMo : IsOpen (M : Set (ProSigmaCompletion P (FreeGroup α))) := N.isOpen.inter N'.isOpen
  haveI : M.Normal := inferInstanceAs (N.toSubgroup ⊓ N'.toSubgroup).Normal
  haveI : Finite (ProSigmaCompletion P (FreeGroup α) ⧸ M) :=
    Subgroup.quotient_finite_of_isOpen M hMo
  have hQ : IsSigmaNat P (Nat.card (ProSigmaCompletion P (FreeGroup α) ⧸ M)) :=
    isSigmaNat_index M hMo
  set Q := ProSigmaCompletion P (FreeGroup α) ⧸ M
  set φ : FreeGroup α →* Q := (QuotientGroup.mk' M).comp (eta P)
  set zb : Q := QuotientGroup.mk z
  have hzb : zb ≠ 1 := by
    intro h
    have : z ∈ M := (QuotientGroup.eq_one_iff z).1 h
    exact hN' this.2 rfl
  have hcomm : ∀ k : FreeGroup α, (QuotientGroup.mk (eta P k) : Q) = 1 →
      z * eta P k = eta P k * z := fun k hk ↦
    hz _ (hN ((QuotientGroup.eq_one_iff _).1 hk).1)
  -- the invariance statement for a family `f` and `k ∈ ker φ`
  have key : ∀ (f : α → Q → ZMod ℓ) (k : FreeGroup α) (d : Q → ZMod ℓ),
      (wrHom φ f k : Equiv.Perm (Q × ZMod ℓ)) = wr 1 d → φ k = 1 → ∀ x, d (zb * x) = d x :=
    fun f k d hk hk1 x ↦ invariant_of_ker P hℓ hP M hMo hQ z hcomm f k hk hk1 x
  -- Step 1: `zb` lies in `⟨φ c⟩` for each generator `c`
  have step1 : ∀ c : α, ∃ i < orderOf (φ (FreeGroup.of c)), φ (FreeGroup.of c) ^ i * zb = 1 := by
    intro c
    set s := φ (FreeGroup.of c)
    have hpos : 0 < orderOf s := orderOf_pos s
    let f : α → Q → ZMod ℓ := fun i ↦ if i = c then delta else 0
    have hk : (wrHom φ f (FreeGroup.of c ^ orderOf s) : Equiv.Perm (Q × ZMod ℓ)) =
        wr 1 (fun x ↦ cnt s x (orderOf s)) := by
      rw [map_pow, Subgroup.coe_pow, wrHom_of, wr_pow, pow_orderOf_eq_one]
      congr 1
      funext x
      simp only [f, if_pos rfl]
      exact sum_delta s x _
    have hk1 : φ (FreeGroup.of c ^ orderOf s) = 1 := by rw [map_pow, pow_orderOf_eq_one]
    have := key f _ _ hk hk1 1
    rw [mul_one, cnt_one hpos le_rfl] at this
    exact exists_of_cnt_eq_one this
  set s := φ (FreeGroup.of a)
  set t := φ (FreeGroup.of b)
  obtain ⟨i, hi, hsi⟩ := step1 a
  obtain ⟨j, -, htj⟩ := step1 b
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hzb (by simpa using hsi)
  set p := orderOf s - i
  have hp0 : 0 < p := Nat.sub_pos_of_lt hi
  have hpm : p < orderOf s := Nat.sub_lt (orderOf_pos s) (Nat.pos_of_ne_zero hi0)
  have hzs : zb = s ^ p := by
    have h1 : s ^ p * s ^ i = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hi.le, pow_orderOf_eq_one]
    calc zb = (s ^ i)⁻¹ := eq_inv_of_mul_eq_one_right hsi
      _ = s ^ p := (eq_inv_of_mul_eq_one_left h1).symm
  have htz : t ^ j = zb⁻¹ := eq_inv_of_mul_eq_one_left htj
  -- Step 2
  let f : α → Q → ZMod ℓ := fun i ↦ if i = a then delta else 0
  set k : FreeGroup α := FreeGroup.of a ^ p * FreeGroup.of b ^ j
  have hk1 : φ k = 1 := by
    simp only [k, map_mul, map_pow]
    rw [htz, ← hzs, mul_inv_cancel]
  have hk : (wrHom φ f k : Equiv.Perm (Q × ZMod ℓ)) = wr 1 (fun x ↦ cnt s (t ^ j * x) p) := by
    simp only [k, map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, wrHom_of, wr_pow, wr_mul]
    have hfb : f b = 0 := by simp [f, Ne.symm hab]
    have hfa : f a = delta := by simp [f]
    rw [hfa, hfb]
    have h1 : s ^ p * t ^ j = 1 := by rw [htz, ← hzs, mul_inv_cancel]
    rw [h1]
    congr 1
    funext x
    simp only [Pi.zero_apply, Finset.sum_const_zero, zero_add]
    exact sum_delta s _ p
  have hinv := key f k _ hk hk1 (zb⁻¹ * (t ^ j)⁻¹)
  have e1 : t ^ j * (zb * (zb⁻¹ * (t ^ j)⁻¹)) = 1 := by group
  have e2 : t ^ j * (zb⁻¹ * (t ^ j)⁻¹) = zb⁻¹ := by
    rw [htz]
    group
  rw [e1, e2, cnt_one hp0 hpm.le] at hinv
  obtain ⟨i', hi', hsi'⟩ := exists_of_cnt_eq_one hinv.symm
  rw [hzs, mul_inv_eq_one] at hsi'
  have := pow_injOn_Iio_orderOf (x := s) (Set.mem_Iio.2 (lt_trans hi' hpm)) (Set.mem_Iio.2 hpm)
    hsi'
  omega

/-- **The pro-`Σ` completion of a free group of rank `≥ 2` is centre-free.** -/
theorem center_eq_bot_freeGroup {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) {a b : α} (hab : a ≠ b) :
    Subgroup.center (ProSigmaCompletion P (FreeGroup α)) = ⊥ :=
  (isSlim_freeGroup hℓ hP hab).center_eq_bot

end ProSigmaCompletion

end Pi1.Profinite

namespace Pi1.SurfaceGroup

open Pi1.Profinite

variable {P : ℕ → Prop} {g r ℓ : ℕ}

/-- `Π^Σ_{g,r+1} ≃ₜ* F(a₁, b₁, …, a_g, b_g, c₁, …, c_r)^Σ`: the pro-`Σ` surface group with a
cusp is free pro-`Σ`. -/
noncomputable def proSigmaFreeEquiv :
    proSigma P g (r + 1) ≃ₜ* ProSigmaCompletion P (FreeGroup (SurfaceGen g r)) :=
  ProSigmaCompletion.congr freeEquiv

/-- **`Π^Σ_{g,r}` is slim** for `(g, r)` hyperbolic with `r ≥ 1` and `Σ` containing a prime `ℓ`:
the vertex groups of `G^Σ` are slim ([SemiAnbd] Def 2.4(ii)). -/
theorem isSlim_proSigma (hr : 0 < r) (h : IsHyperbolic g r) (hℓ : ℓ.Prime) (hP : P ℓ) :
    IsSlim (proSigma P g r) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  refine IsSlim.of_continuousMulEquiv proSigmaFreeEquiv.symm ?_
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hr2 : 1 < r := by unfold IsHyperbolic at h; omega
    exact ProSigmaCompletion.isSlim_freeGroup hℓ hP (a := SurfaceGen.c ⟨0, by omega⟩)
      (b := SurfaceGen.c ⟨1, hr2⟩) (by simp)
  · exact ProSigmaCompletion.isSlim_freeGroup hℓ hP (a := SurfaceGen.a ⟨0, hg⟩)
      (b := SurfaceGen.b ⟨0, hg⟩) (by simp)

/-- **`Π^Σ_{g,r}` is centre-free** for `(g, r)` hyperbolic with `r ≥ 1` and `Σ` containing a
prime. -/
theorem center_proSigma_eq_bot (hr : 0 < r) (h : IsHyperbolic g r) (hℓ : ℓ.Prime) (hP : P ℓ) :
    Subgroup.center (proSigma P g r) = ⊥ :=
  (isSlim_proSigma hr h hℓ hP).center_eq_bot

end Pi1.SurfaceGroup
