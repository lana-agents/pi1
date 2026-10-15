/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Profinite.Completion
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Slimness of free profinite groups

A topological group `H` is **slim** if every open subgroup of `H` has trivial centraliser
(Mochizuki, *The absolute anabelian geometry of canonical curves*, §0; *Topics in absolute
anabelian geometry I*, §0). We prove that the profinite completion of a free group on a type with
at least two elements is slim (`Pi1.Profinite.isSlim_completion_freeGroup`); in particular its
centre is trivial (`IsSlim.center_eq_bot`).

## The argument

Let `F` be free on `α ∋ a ≠ b`, `F̂` its profinite completion, and suppose `z ≠ 1` centralises an
open subgroup `U`. Choose an open normal `M ⊆ U` with `z ∉ M`, put `Q = F̂ / M` (finite),
`φ : F → Q` and `z̄ ≠ 1` the image of `z`. Every family `f : α → (Q → 𝔽₂)` defines a homomorphism
`ψ_f : F → Perm (Q × 𝔽₂)`, `ψ_f(x) = wr (φ x) (f x)`, where
`wr q f (y, c) = (q y, c + f y)` (an element of the wreath product `𝔽₂ ≀ Q`). For `k ∈ ker φ`
one has `ψ_f(k) = wr 1 d` for some `d : Q → 𝔽₂`, and since `z` commutes with `k` in `F̂`, the
continuous extension of `ψ_f` shows `d (z̄ y) = d y` for all `y` (`invariant_of_ker`).

* With `f = δ₁` at `a` and `0` elsewhere and `k = a ^ ord(s)` (`s = φ a`), `d` is the indicator
  of `⟨s⟩`, so `z̄ ∈ ⟨s⟩`; likewise `z̄ ∈ ⟨t⟩` for `t = φ b`. Write `z̄ = s ^ p` with
  `0 < p < ord(s)` and `z̄ = t ^ (-j)`.
* With the same `f` and `k = a ^ p b ^ j ∈ ker φ`, `d y` is the indicator of
  `t ^ (-j) {s ^ (-i) | i < p}`; its invariance under `z̄` forces `s ^ (p - i) = 1` for some
  `i < p`, contradicting `p < ord(s)`.

This is the wreath-product (Magnus-embedding) form of the classical fact that `ker φ` acts on
its own `𝔽₂`-abelianisation through a free `𝔽₂[Q]`-summand, without Nielsen–Schreier.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology

universe u

namespace Pi1.Profinite

/-- A topological group is **slim** if every open subgroup has trivial centraliser. -/
def IsSlim (H : Type*) [Group H] [TopologicalSpace H] : Prop :=
  ∀ (U : OpenSubgroup H) (z : H), (∀ u ∈ U, z * u = u * z) → z = 1

/-- A slim group has trivial centre. -/
theorem IsSlim.center_eq_bot {H : Type*} [Group H] [TopologicalSpace H] (h : IsSlim H) :
    Subgroup.center H = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ h ⊤ z fun u _ ↦ ?_
  exact (Subgroup.mem_center_iff.1 hz u).symm

/-- Slimness transfers along isomorphisms of topological groups. -/
theorem IsSlim.of_continuousMulEquiv {H K : Type*} [Group H] [TopologicalSpace H] [Group K]
    [TopologicalSpace K] (e : H ≃ₜ* K) (h : IsSlim H) : IsSlim K := by
  intro U z hz
  have hU : IsOpen (e ⁻¹' (U : Set K)) := U.isOpen.preimage e.continuous
  let V : OpenSubgroup H := ⟨U.toSubgroup.comap e.toMonoidHom, hU⟩
  have : e.symm z = 1 := h V (e.symm z) fun v hv ↦ by
    apply e.injective
    simpa using hz (e v) hv
  simpa using congrArg e this

/-! ### The wreath product `𝔽₂ ≀ Q` as permutations of `Q × 𝔽₂` -/

namespace Wreath

variable {Q : Type u} [Group Q]

/-- The permutation `(y, c) ↦ (q y, c + f y)` of `Q × 𝔽₂`. -/
def wr (q : Q) (f : Q → ZMod 2) : Equiv.Perm (Q × ZMod 2) where
  toFun p := (q * p.1, p.2 + f p.1)
  invFun p := (q⁻¹ * p.1, p.2 - f (q⁻¹ * p.1))
  left_inv p := by simp
  right_inv p := by simp

@[simp]
lemma wr_apply (q : Q) (f : Q → ZMod 2) (p : Q × ZMod 2) : wr q f p = (q * p.1, p.2 + f p.1) :=
  rfl

lemma wr_mul (q q' : Q) (f f' : Q → ZMod 2) :
    wr q f * wr q' f' = wr (q * q') (fun x ↦ f' x + f (q' * x)) := by
  ext p
  · simp [mul_assoc]
  · simp [add_assoc]

lemma wr_injective {q q' : Q} {f f' : Q → ZMod 2} (h : wr q f = wr q' f') : q = q' ∧ f = f' := by
  refine ⟨?_, funext fun x ↦ ?_⟩
  · simpa using congrArg Prod.fst (Equiv.ext_iff.1 h (1, 0))
  · simpa using congrArg Prod.snd (Equiv.ext_iff.1 h (x, 0))

lemma wr_one_zero : wr (1 : Q) 0 = 1 := by
  ext p <;> simp

lemma wr_inv (q : Q) (f : Q → ZMod 2) : (wr q f)⁻¹ = wr q⁻¹ (fun x ↦ -f (q⁻¹ * x)) := by
  rw [inv_eq_iff_mul_eq_one, wr_mul, ← wr_one_zero]
  congr 1
  · simp
  · funext x
    simp

lemma wr_pow (q : Q) (f : Q → ZMod 2) (n : ℕ) :
    wr q f ^ n = wr (q ^ n) (fun x ↦ ∑ i ∈ Finset.range n, f (q ^ i * x)) := by
  induction n with
  | zero =>
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty]
    exact wr_one_zero.symm
  | succ n ih =>
    rw [pow_succ, ih, wr_mul, pow_succ]
    congr 1
    funext x
    rw [Finset.sum_range_succ', pow_zero, one_mul, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pow_succ, mul_assoc]

/-- If `wr z e` commutes with `wr 1 d`, then `d` is invariant under left translation by `z`. -/
lemma invariant_of_commute {z : Q} {e d : Q → ZMod 2} (h : wr z e * wr 1 d = wr 1 d * wr z e)
    (x : Q) : d (z * x) = d x := by
  rw [wr_mul, wr_mul] at h
  have := congrFun (wr_injective h).2 x
  simp only [one_mul] at this
  rw [add_comm] at this
  exact (add_left_cancel this).symm

section Count

open Classical

/-- The indicator of `1 : Q`. -/
noncomputable def delta : Q → ZMod 2 := fun x ↦ if x = 1 then 1 else 0

/-- The number of `i < n` with `s ^ i * y = 1`, modulo `2`. -/
noncomputable def cnt (s y : Q) (n : ℕ) : ZMod 2 :=
  ((Finset.range n).filter fun i ↦ s ^ i * y = 1).card

lemma sum_delta (s y : Q) (n : ℕ) :
    ∑ i ∈ Finset.range n, delta (s ^ i * y) = cnt s y n := by
  classical
  simp only [delta, cnt]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma exists_of_cnt_eq_one {s y : Q} {n : ℕ} (h : cnt s y n = 1) : ∃ i < n, s ^ i * y = 1 := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have : (Finset.range n).filter (fun i ↦ s ^ i * y = 1) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun i hi ↦ hne i (Finset.mem_range.1 hi)
  rw [cnt, this, Finset.card_empty, Nat.cast_zero] at h
  exact absurd h (by decide)

lemma cnt_one {s : Q} {n : ℕ} (hn : 0 < n) (hs : n ≤ orderOf s) : cnt s 1 n = 1 := by
  have : (Finset.range n).filter (fun i ↦ s ^ i * 1 = 1) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, mul_one, Finset.mem_singleton]
    constructor
    · rintro ⟨hi, h⟩
      by_contra h0
      exact pow_ne_one_of_lt_orderOf h0 (lt_of_lt_of_le hi hs) h
    · rintro rfl
      exact ⟨hn, pow_zero s⟩
  rw [cnt, this, Finset.card_singleton, Nat.cast_one]

end Count

end Wreath

open Wreath

/-! ### The main argument -/

section Free

variable {α : Type u}

/-- The homomorphism `F(α) → Perm (Q × 𝔽₂)`, `x ↦ wr (φ x) (f x)`. -/
noncomputable def wrHom {Q : Type u} [Group Q] (φ : FreeGroup α →* Q) (f : α → Q → ZMod 2) :
    FreeGroup α →* Equiv.Perm (Q × ZMod 2) :=
  FreeGroup.lift fun i ↦ wr (φ (FreeGroup.of i)) (f i)

lemma wrHom_eq {Q : Type u} [Group Q] (φ : FreeGroup α →* Q) (f : α → Q → ZMod 2)
    (w : FreeGroup α) : ∃ d, wrHom φ f w = wr (φ w) d := by
  induction w using FreeGroup.induction_on with
  | C1 => exact ⟨0, by simp [wr_one_zero]⟩
  | of i => exact ⟨f i, by simp [wrHom]⟩
  | inv_of i _ =>
    exact ⟨fun x ↦ -f i ((φ (FreeGroup.of i))⁻¹ * x), by simp [wrHom, wr_inv]⟩
  | mul x y hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨_, by rw [map_mul, hd, hd', wr_mul, map_mul]⟩

lemma wrHom_of {Q : Type u} [Group Q] (φ : FreeGroup α →* Q) (f : α → Q → ZMod 2) (i : α) :
    wrHom φ f (FreeGroup.of i) = wr (φ (FreeGroup.of i)) (f i) := by
  simp [wrHom]

variable (α) in
/-- The profinite completion of the free group on `α`. -/
noncomputable abbrev FreeHat : ProfiniteGrp.{u} := completion (GrpCat.of (FreeGroup α))

/-- **Invariance of cocycles under a centralising element.** Let `M` be an open normal subgroup
of `F̂(α)`, `φ : F(α) → F̂ / M`, and let `z` commute with every element of the image of `ker φ`.
Then for every `f` and every `k ∈ ker φ`, writing `wrHom φ f k = wr 1 d`, the function `d` is
invariant under translation by the image of `z`. -/
lemma invariant_of_ker (M : Subgroup (FreeHat α)) [M.Normal] (hM : IsOpen (M : Set (FreeHat α)))
    [Finite (FreeHat α ⧸ M)] (z : FreeHat α)
    (hz : ∀ k : FreeGroup α, (QuotientGroup.mk (etaFn _ k) : FreeHat α ⧸ M) = 1 →
      z * etaFn _ k = etaFn _ k * z)
    (f : α → (FreeHat α ⧸ M) → ZMod 2) (k : FreeGroup α) {d : (FreeHat α ⧸ M) → ZMod 2}
    (hk : wrHom ((QuotientGroup.mk' M).comp (eta (GrpCat.of (FreeGroup α))).hom) f k = wr 1 d)
    (hk1 : (QuotientGroup.mk (etaFn _ k) : FreeHat α ⧸ M) = 1) (x : FreeHat α ⧸ M) :
    d (QuotientGroup.mk z * x) = d x := by
  set φ := (QuotientGroup.mk' M).comp (eta (GrpCat.of (FreeGroup α))).hom
  set ψ := wrHom φ f
  obtain ⟨x₀, hx₀, hψ⟩ := exists_etaFn_eq ψ (isOpen_setOf_mk_eq M hM z) (z := z) rfl
  obtain ⟨e, he⟩ := wrHom_eq φ f x₀
  have hφ : φ x₀ = QuotientGroup.mk z := hx₀
  have hz' : liftFinite ψ z = wr (QuotientGroup.mk z) e := by rw [← hψ, he, hφ]
  have hc := congrArg (liftFinite ψ) (hz k hk1)
  rw [map_mul, map_mul, liftFinite_eta, hk, hz'] at hc
  exact invariant_of_commute hc x

/-- **The profinite completion of a free group of rank `≥ 2` is slim.** -/
theorem isSlim_completion_freeGroup {a b : α} (hab : a ≠ b) : IsSlim (FreeHat α) := by
  classical
  intro U z hz
  by_contra hz1
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one U.isOpen
    U.one_mem
  obtain ⟨N', hN'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := z)) (by simpa [eq_comm] using hz1)
  set M : Subgroup (FreeHat α) := N.toSubgroup ⊓ N'.toSubgroup with hMdef
  have hMo : IsOpen (M : Set (FreeHat α)) := N.isOpen.inter N'.isOpen
  haveI : M.Normal := inferInstanceAs (N.toSubgroup ⊓ N'.toSubgroup).Normal
  haveI : Finite (FreeHat α ⧸ M) := Subgroup.quotient_finite_of_isOpen M hMo
  set Q := FreeHat α ⧸ M
  set φ : FreeGroup α →* Q := (QuotientGroup.mk' M).comp (eta (GrpCat.of (FreeGroup α))).hom
  have hφ : ∀ w, φ w = QuotientGroup.mk (etaFn _ w) := fun _ ↦ rfl
  set zb : Q := QuotientGroup.mk z
  have hzb : zb ≠ 1 := by
    intro h
    have : z ∈ M := (QuotientGroup.eq_one_iff z).1 h
    exact hN' this.2 rfl
  have hcomm : ∀ k : FreeGroup α, (QuotientGroup.mk (etaFn _ k) : Q) = 1 →
      z * etaFn _ k = etaFn _ k * z := fun k hk ↦
    hz _ (hN ((QuotientGroup.eq_one_iff _).1 hk).1)
  -- the invariance statement for a family `f` and `k ∈ ker φ`
  have key : ∀ (f : α → Q → ZMod 2) (k : FreeGroup α) (d : Q → ZMod 2),
      wrHom φ f k = wr 1 d → φ k = 1 → ∀ x, d (zb * x) = d x :=
    fun f k d hk hk1 x ↦ invariant_of_ker M hMo z hcomm f k hk hk1 x
  -- Step 1: `zb` lies in `⟨φ c⟩` for each generator `c`
  have step1 : ∀ c : α, ∃ i < orderOf (φ (FreeGroup.of c)), φ (FreeGroup.of c) ^ i * zb = 1 := by
    intro c
    set s := φ (FreeGroup.of c)
    have hpos : 0 < orderOf s := orderOf_pos s
    let f : α → Q → ZMod 2 := fun i ↦ if i = c then delta else 0
    have hk : wrHom φ f (FreeGroup.of c ^ orderOf s) = wr 1 (fun x ↦ cnt s x (orderOf s)) := by
      rw [map_pow, wrHom_of, wr_pow, pow_orderOf_eq_one]
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
  let f : α → Q → ZMod 2 := fun i ↦ if i = a then delta else 0
  set k : FreeGroup α := FreeGroup.of a ^ p * FreeGroup.of b ^ j
  have hk1 : φ k = 1 := by
    simp only [k, map_mul, map_pow]
    rw [htz, ← hzs, mul_inv_cancel]
  have hk : wrHom φ f k = wr 1 (fun x ↦ cnt s (t ^ j * x) p) := by
    simp only [k, map_mul, map_pow, wrHom_of, wr_pow, wr_mul]
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

end Free

end Pi1.Profinite
