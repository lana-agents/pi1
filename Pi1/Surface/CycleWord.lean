/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group

/-!
# Words along the cycles of a permutation

For a permutation `π` of a finite set `D` and a labelling `lab : D → G` with values in a group, the
*path word* of length `n` starting at `x` is `lab (πⁿ⁻¹ x) ⋯ lab (π x) · lab x`, and the *cycle
word* of `x` is the path word of the length of the cycle of `x` (`Pi1.Ribbon.faceWord`). Along a
cycle the cycle words are conjugate (`isConj_faceWord_of_sameCycle`).

This file proves the two pieces of permutation combinatorics behind deleting an edge of a ribbon
graph (`Pi1.Surface.RibbonGraph`):

* `skip π h = swap h (π h) * π` removes `h` from its cycle; the other cycles are unchanged and, if
  `lab h = 1`, so are all cycle words (`sameCycle_skip_iff`, `faceWord_skip`);
* multiplying on the right by a transposition `swap a b` merges the cycles of `a` and `b` if they
  are distinct (`Merge`) and splits their common cycle otherwise (`Split`), with explicit cycle
  words.
-/

@[expose] public section

namespace Pi1.Ribbon

open Equiv Function

variable {D : Type*}

/-! ### Periods -/

section Period

variable [Finite D] (π : Perm D) (x : D)

/-- The length of the cycle of `x`. -/
noncomputable abbrev per : ℕ := minimalPeriod π x

lemma mem_periodicPts : x ∈ periodicPts π :=
  ⟨orderOf π, orderOf_pos π, by
    change ⇑(π ^ orderOf π) x = x
    rw [pow_orderOf_eq_one]; rfl⟩

lemma per_pos : 0 < per π x := minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts π x)

omit [Finite D] in
lemma pow_per : (π ^ per π x) x = x := iterate_minimalPeriod

variable {π x}

omit [Finite D] in
lemma pow_ne_self {k : ℕ} (hk : 0 < k) (hk' : k < per π x) : (π ^ k) x ≠ x :=
  not_isPeriodicPt_of_pos_of_lt_minimalPeriod hk.ne' hk'

omit [Finite D] in
lemma pow_mod_per (k : ℕ) : (π ^ (k % per π x)) x = (π ^ k) x := iterate_mod_minimalPeriod_eq

omit [Finite D] in
lemma pow_inj {i j : ℕ} (hi : i < per π x) (hj : j < per π x) (h : (π ^ i) x = (π ^ j) x) :
    i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi h.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have h' : (π ^ i) ((π ^ d) x) = (π ^ i) x := by
    rw [← Perm.mul_apply, ← pow_add, ← h]
  have hd : (π ^ d) x = x := (π ^ i).injective h'
  by_contra hne
  exact pow_ne_self (by omega) (by omega) hd

lemma exists_lt_per {y : D} (h : π.SameCycle x y) : ∃ j < per π x, (π ^ j) x = y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  exact ⟨k % per π x, Nat.mod_lt _ (per_pos π x), pow_mod_per k⟩

lemma per_eq {n : ℕ} (hn : 0 < n) (hx : (π ^ n) x = x)
    (hne : ∀ k, 0 < k → k < n → (π ^ k) x ≠ x) : per π x = n := by
  have hle : per π x ≤ n := IsPeriodicPt.minimalPeriod_le hn hx
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd (pow_per π x) (hne _ (per_pos π x) hlt)
  · exact heq

lemma per_apply : per π (π x) = per π x := minimalPeriod_apply (mem_periodicPts π x)

omit [Finite D] in
lemma sameCycle_pow (k : ℕ) : π.SameCycle x ((π ^ k) x) := ⟨k, by simp⟩

end Period

/-! ### Path words and cycle words -/

section Words

variable {G : Type*} [Group G]

/-- The path word `lab (πⁿ⁻¹ x) ⋯ lab (π x) · lab x`. -/
def pathWord (π : Perm D) (lab : D → G) (x : D) : ℕ → G
  | 0 => 1
  | n + 1 => lab ((π ^ n) x) * pathWord π lab x n

variable (π : Perm D) (lab : D → G) (x : D)

@[simp] lemma pathWord_zero : pathWord π lab x 0 = 1 := rfl

lemma pathWord_succ (n : ℕ) : pathWord π lab x (n + 1) = lab ((π ^ n) x) * pathWord π lab x n :=
  rfl

@[simp] lemma pathWord_one : pathWord π lab x 1 = lab x := by
  simp [pathWord_succ]

lemma pathWord_add (m n : ℕ) :
    pathWord π lab x (m + n) = pathWord π lab ((π ^ m) x) n * pathWord π lab x m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, pathWord_succ, ih, pathWord_succ, mul_assoc, add_comm m n, pow_add,
      Perm.mul_apply]

variable {π lab x} in
lemma pathWord_congr {H D' : Type*} [Group H] {ρ : Perm D'} {lab' : D' → H} {y : D'} {n : ℕ}
    (f : G →* H) (h : ∀ i < n, lab' ((ρ ^ i) y) = f (lab ((π ^ i) x))) :
    pathWord ρ lab' y n = f (pathWord π lab x n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pathWord_succ, pathWord_succ, map_mul, h n (by omega), ih (fun i hi ↦ h i (by omega))]

variable {π lab x} in
lemma pathWord_congr' {D' : Type*} {ρ : Perm D'} {lab' : D' → G} {y : D'} {n : ℕ}
    (h : ∀ i < n, lab' ((ρ ^ i) y) = lab ((π ^ i) x)) :
    pathWord ρ lab' y n = pathWord π lab x n :=
  pathWord_congr (MonoidHom.id G) h

/-- The cycle word of `x`: the path word once around the cycle of `x`. -/
noncomputable def faceWord [Finite D] : G := pathWord π lab x (per π x)

variable [Finite D]

lemma faceWord_eq_pathWord_succ :
    faceWord π lab x = pathWord π lab (π x) (per π x - 1) * lab x := by
  have h := pathWord_add π lab x 1 (per π x - 1)
  rw [show 1 + (per π x - 1) = per π x by have := per_pos π x; omega, pow_one,
    pathWord_one] at h
  exact h

lemma faceWord_apply :
    faceWord π lab (π x) = lab x * faceWord π lab x * (lab x)⁻¹ := by
  have h1 := pathWord_add π lab x 1 (per π x)
  have h2 := pathWord_succ π lab x (per π x)
  rw [pow_per, add_comm] at h2
  rw [h2, pow_one, pathWord_one] at h1
  rw [faceWord, faceWord, per_apply, h1]
  group

lemma isConj_faceWord_apply : IsConj (faceWord π lab x) (faceWord π lab (π x)) := by
  rw [faceWord_apply]
  exact isConj_iff.2 ⟨lab x, rfl⟩

variable {π x} in
lemma isConj_faceWord_of_sameCycle {y : D} (h : π.SameCycle x y) :
    IsConj (faceWord π lab x) (faceWord π lab y) := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => exact IsConj.refl _
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (isConj_faceWord_apply π lab _)

lemma map_faceWord {H F : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (f : F) :
    faceWord π (f ∘ lab) x = f (faceWord π lab x) :=
  pathWord_congr (f : G →* H) fun _ _ ↦ rfl

omit [Finite D] in
/-- If two permutations agree along the first `n` steps from `x`, so do their iterates. -/
lemma pow_eq_of_agree {ρ : Perm D} {n : ℕ} (h : ∀ i < n, ρ ((π ^ i) x) = π ((π ^ i) x)) :
    ∀ i ≤ n, (ρ ^ i) x = (π ^ i) x := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply, ih (by omega), h i (by omega), pow_succ', Perm.mul_apply]

/-- Two permutations that agree on the whole cycle of `x` have the same cycle words at `x`. -/
lemma faceWord_eq_of_agree {ρ : Perm D} {lab' : D → G} (h : ∀ i, ρ ((π ^ i) x) = π ((π ^ i) x))
    (hl : ∀ i, lab' ((π ^ i) x) = lab ((π ^ i) x)) :
    per ρ x = per π x ∧ faceWord ρ lab' x = faceWord π lab x := by
  have hp : ∀ i, (ρ ^ i) x = (π ^ i) x := fun i ↦
    pow_eq_of_agree π x (n := i) (fun j _ ↦ h j) i le_rfl
  have hper : per ρ x = per π x := by
    refine per_eq (per_pos π x) (by rw [hp, pow_per]) fun k hk hk' ↦ ?_
    rw [hp]
    exact pow_ne_self hk hk'
  refine ⟨hper, ?_⟩
  rw [faceWord, faceWord, hper]
  exact pathWord_congr' fun i _ ↦ by rw [hp, hl]

lemma sameCycle_iff_of_agree {ρ : Perm D} (h : ∀ i, ρ ((π ^ i) x) = π ((π ^ i) x)) (y : D) :
    ρ.SameCycle x y ↔ π.SameCycle x y := by
  have hp : ∀ i, (ρ ^ i) x = (π ^ i) x := fun i ↦
    pow_eq_of_agree π x (n := i) (fun j _ ↦ h j) i le_rfl
  constructor
  · intro hs
    obtain ⟨k, rfl⟩ := hs.exists_nat_pow_eq
    rw [hp]; exact sameCycle_pow k
  · intro hs
    obtain ⟨k, rfl⟩ := hs.exists_nat_pow_eq
    rw [← hp]; exact sameCycle_pow k

lemma faceWord_subtypePerm {p : D → Prop} (hp : ∀ x, p (π x) ↔ p x) (lab : D → G)
    (x : Subtype p) :
    faceWord (π.subtypePerm hp) (lab ∘ Subtype.val) x = faceWord π lab x.1 := by
  have hpow : ∀ i, ((π.subtypePerm hp ^ i) x).1 = (π ^ i) x.1 := fun i ↦ by
    rw [Perm.subtypePerm_pow]; rfl
  have hper : per (π.subtypePerm hp) x = per π x.1 := by
    refine (per_eq (per_pos π x.1) (Subtype.ext ?_) fun k hk hk' h ↦ ?_)
    · rw [hpow, pow_per]
    · exact pow_ne_self hk hk' (by rw [← hpow, h])
  rw [faceWord, faceWord, hper]
  exact pathWord_congr' (π := π) (lab := lab) (x := x.1) fun i _ ↦ by simp

omit [Finite D] in
lemma sameCycle_subtypePerm_iff {p : D → Prop} (hp : ∀ x, p (π x) ↔ p x) (x y : Subtype p) :
    (π.subtypePerm hp).SameCycle x y ↔ π.SameCycle x.1 y.1 :=
  Perm.sameCycle_subtypePerm

end Words

/-! ### Removing a point from its cycle -/

section Skip

variable [DecidableEq D] (π : Perm D) (h : D)

/-- `skip π h` removes `h` from its cycle (and fixes `h`). -/
def skip : Perm D := swap h (π h) * π

@[simp] lemma skip_apply_self : skip π h h = h := by
  simp [skip, swap_apply_right]

variable {π h}

lemma skip_apply_of_eq {x : D} (hx : π x = h) : skip π h x = π h := by
  simp [skip, hx, swap_apply_left]

lemma skip_apply_of_ne {x : D} (hx : x ≠ h) (hπx : π x ≠ h) : skip π h x = π x := by
  simp only [skip, Perm.mul_apply]
  exact swap_apply_of_ne_of_ne hπx (π.injective.ne hx)

lemma skip_apply_eq_ite {x : D} (hx : x ≠ h) :
    skip π h x = if π x = h then π h else π x := by
  split_ifs with h'
  · exact skip_apply_of_eq h'
  · exact skip_apply_of_ne hx h'

lemma skip_apply_ne {x : D} (hx : x ≠ h) : skip π h x ≠ h := by
  by_cases h' : π x = h
  · rw [skip_apply_of_eq h']
    intro h''
    exact hx (π.injective (h'.trans h''.symm))
  · rwa [skip_apply_of_ne hx h']

lemma exists_pow_skip (x : D) (k : ℕ) : ∃ k' : ℕ, (skip π h ^ k) x = (π ^ k') x := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨k', hk'⟩ := ih
    rw [pow_succ', Perm.mul_apply, hk']
    by_cases h1 : (π ^ k') x = h
    · exact ⟨k', by rw [h1, skip_apply_self]⟩
    by_cases h2 : π ((π ^ k') x) = h
    · refine ⟨k' + 2, ?_⟩
      rw [skip_apply_of_eq h2, ← h2, show k' + 2 = k' + 1 + 1 from rfl, pow_succ', pow_succ']
      rfl
    · exact ⟨k' + 1, by rw [skip_apply_of_ne h1 h2, pow_succ', Perm.mul_apply]⟩

lemma skip_pow_lt {x : D} {k : ℕ} (hk : ∀ i ≤ k, (π ^ i) x ≠ h) :
    (skip π h ^ k) x = (π ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih (fun i hi ↦ hk i (by omega)),
      skip_apply_of_ne (hk k (by omega)) (by rw [← Perm.mul_apply, ← pow_succ']; exact hk _ le_rfl),
      pow_succ', Perm.mul_apply]

lemma skip_pow_ge {x : D} {j : ℕ} (hj : (π ^ j) x = h) (hj0 : 0 < j)
    (hbefore : ∀ i < j, (π ^ i) x ≠ h) (k : ℕ)
    (hafter : ∀ i, j < i → i ≤ j + 1 + k → (π ^ i) x ≠ h) :
    (skip π h ^ (j + k)) x = (π ^ (j + k + 1)) x := by
  induction k with
  | zero =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [add_zero]
    rw [pow_succ', Perm.mul_apply, skip_pow_lt (fun i hi ↦ hbefore i (by omega))]
    have h' : π ((π ^ j') x) = h := by rw [← Perm.mul_apply, ← pow_succ', hj]
    rw [skip_apply_of_eq h', ← hj, pow_succ' π (j' + 1), Perm.mul_apply]
  | succ k ih =>
    rw [← add_assoc, pow_succ', Perm.mul_apply, ih (fun i hi hi' ↦ hafter i hi (by omega)),
      skip_apply_of_ne (hafter _ (by omega) (by omega))
        (by rw [← Perm.mul_apply, ← pow_succ']; exact hafter _ (by omega) (by omega)),
      ← Perm.mul_apply, ← pow_succ']

variable [Finite D]

/-- The structure of the cycle of `x ≠ h` in `skip π h`, when `h` lies on it. -/
lemma skip_cycle {x : D} (hx : x ≠ h) (hxh : π.SameCycle x h) :
    ∃ j, 0 < j ∧ j < per π x ∧ (π ^ j) x = h ∧ (∀ i < j, (skip π h ^ i) x = (π ^ i) x) ∧
      (∀ k, j + k < per π x → (skip π h ^ (j + k)) x = (π ^ (j + k + 1)) x) := by
  obtain ⟨j, hjm, hj⟩ := exists_lt_per hxh
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h0
    · exact absurd hj hx
    · exact h0
  have hne : ∀ i < per π x, i ≠ j → (π ^ i) x ≠ h := fun i hi hij h' ↦
    hij (pow_inj hi hjm (h'.trans hj.symm))
  refine ⟨j, hj0, hjm, hj, fun i hi ↦ skip_pow_lt fun i' hi' ↦ hne i' (by omega) (by omega),
    fun k hk ↦ skip_pow_ge hj hj0 (fun i hi ↦ hne i (by omega) (by omega)) k fun i hi hi' ↦ ?_⟩
  rcases (Nat.lt_or_ge i (per π x)) with h1 | h1
  · exact hne i h1 (by omega)
  · have : i = per π x := by omega
    rw [this, pow_per]; exact hx

lemma sameCycle_skip_iff {x y : D} (hx : x ≠ h) (hy : y ≠ h) :
    (skip π h).SameCycle x y ↔ π.SameCycle x y := by
  constructor
  · intro hs
    obtain ⟨k, rfl⟩ := hs.exists_nat_pow_eq
    obtain ⟨k', hk'⟩ := exists_pow_skip (π := π) (h := h) x k
    rw [hk']; exact sameCycle_pow k'
  · intro hs
    by_cases hxh : π.SameCycle x h
    · obtain ⟨j, hj0, hjm, hj, hlt, hge⟩ := skip_cycle hx hxh
      obtain ⟨i, him, rfl⟩ := exists_lt_per hs
      rcases Nat.lt_or_ge i j with hij | hij
      · rw [← hlt i hij]; exact sameCycle_pow i
      · have hij' : i ≠ j := fun h' ↦ hy (h' ▸ hj)
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (lt_of_le_of_ne hij (Ne.symm hij'))
        rw [← hge k (by omega)]; exact sameCycle_pow _
    · have hagree : ∀ i, skip π h ((π ^ i) x) = π ((π ^ i) x) := fun i ↦
        skip_apply_of_ne (fun h' ↦ hxh (h' ▸ sameCycle_pow i))
          (fun h' ↦ hxh (by rw [← h', ← Perm.mul_apply, ← pow_succ']; exact sameCycle_pow _))
      exact (sameCycle_iff_of_agree π x hagree y).2 hs

variable {G : Type*} [Group G]

lemma faceWord_skip {lab : D → G} (hlab : lab h = 1) {x : D} (hx : x ≠ h) :
    faceWord (skip π h) lab x = faceWord π lab x := by
  by_cases hxh : π.SameCycle x h
  · obtain ⟨j, hj0, hjm, hj, hlt, hge⟩ := skip_cycle hx hxh
    obtain ⟨k, hk⟩ : ∃ k, per π x = j + 1 + k := ⟨per π x - j - 1, by omega⟩
    have hper : per (skip π h) x = j + k := by
      refine per_eq (by omega) ?_ fun i hi hi' ↦ ?_
      · rw [hge k (by omega), show j + k + 1 = per π x by omega, pow_per]
      · rcases Nat.lt_or_ge i j with hij | hij
        · rw [hlt i hij]; exact pow_ne_self hi (by omega)
        · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hij
          rw [hge i' (by omega)]; exact pow_ne_self (by omega) (by omega)
    have hL : pathWord (skip π h) lab x (j + k) =
        pathWord (skip π h) lab ((skip π h ^ j) x) k * pathWord (skip π h) lab x j :=
      pathWord_add _ _ _ _ _
    have hR : pathWord π lab x (j + 1 + k) =
        pathWord π lab ((π ^ (j + 1)) x) k * (lab ((π ^ j) x) * pathWord π lab x j) := by
      rw [pathWord_add, pathWord_succ]
    rw [faceWord, faceWord, hper, hk, hL, hR, hj, hlab, one_mul]
    congr 1
    · refine pathWord_congr' fun i hi ↦ ?_
      rw [← Perm.mul_apply, ← pow_add, ← Perm.mul_apply, ← pow_add, add_comm i j,
        hge i (by omega), show j + i + 1 = i + (j + 1) by omega]
    · exact pathWord_congr' fun i hi ↦ by rw [hlt i hi]
  · have hagree : ∀ i, skip π h ((π ^ i) x) = π ((π ^ i) x) := fun i ↦
      skip_apply_of_ne (fun h' ↦ hxh (h' ▸ sameCycle_pow i))
        (fun h' ↦ hxh (by rw [← h', ← Perm.mul_apply, ← pow_succ']; exact sameCycle_pow _))
    exact (faceWord_eq_of_agree π lab x hagree fun _ ↦ rfl).2

end Skip

/-! ### Multiplying by a transposition -/

section Swap

variable [DecidableEq D] (φ : Perm D) {a b : D}

lemma mul_swap_apply_left : (φ * swap a b) a = φ b := by simp

lemma mul_swap_apply_right : (φ * swap a b) b = φ a := by simp

lemma mul_swap_apply_of_ne {y : D} (hya : y ≠ a) (hyb : y ≠ b) : (φ * swap a b) y = φ y := by
  simp [swap_apply_of_ne_of_ne hya hyb]

lemma pow_mul_swap_eq {x : D} {n : ℕ} (h : ∀ i < n, (φ ^ i) x ≠ a ∧ (φ ^ i) x ≠ b) :
    ∀ i ≤ n, ((φ * swap a b) ^ i) x = (φ ^ i) x :=
  pow_eq_of_agree φ x fun i hi ↦ mul_swap_apply_of_ne φ (h i hi).1 (h i hi).2

variable [Finite D] {G : Type*} [Group G]

omit [Finite D] in
/-- Cycles avoiding `a` and `b` are not affected by `* swap a b`. -/
lemma mul_swap_agree {x : D} (ha : ¬ φ.SameCycle x a) (hb : ¬ φ.SameCycle x b) (i : ℕ) :
    (φ * swap a b) ((φ ^ i) x) = φ ((φ ^ i) x) :=
  mul_swap_apply_of_ne φ (fun h ↦ ha (h ▸ sameCycle_pow i)) (fun h ↦ hb (h ▸ sameCycle_pow i))

lemma sameCycle_mul_swap_iff_of_not {x : D} (ha : ¬ φ.SameCycle x a) (hb : ¬ φ.SameCycle x b)
    (y : D) : (φ * swap a b).SameCycle x y ↔ φ.SameCycle x y :=
  sameCycle_iff_of_agree φ x (mul_swap_agree φ ha hb) y

lemma faceWord_mul_swap_of_not {lab lab₀ : D → G} (hl : ∀ y, y ≠ a → y ≠ b → lab₀ y = lab y)
    {x : D} (ha : ¬ φ.SameCycle x a) (hb : ¬ φ.SameCycle x b) :
    faceWord (φ * swap a b) lab₀ x = faceWord φ lab x :=
  (faceWord_eq_of_agree φ lab x (mul_swap_agree φ ha hb) fun i ↦
    hl _ (fun h ↦ ha (h ▸ sameCycle_pow i)) (fun h ↦ hb (h ▸ sameCycle_pow i))).2

/-- **Merging** two cycles: if `a` and `b` lie on distinct cycles of `φ`, they lie on one cycle
of `φ * swap a b`, which is the union of the two, and (with the letters at `a`, `b` erased) its
word is the product of the two words with the letters at `a`, `b` removed. -/
lemma merge {lab lab₀ : D → G} (hab : ¬ φ.SameCycle a b) (hla : lab₀ a = 1) (hlb : lab₀ b = 1)
    (hl : ∀ y, y ≠ a → y ≠ b → lab₀ y = lab y) :
    (∀ x, (φ * swap a b).SameCycle a x ↔ φ.SameCycle a x ∨ φ.SameCycle b x) ∧
      faceWord (φ * swap a b) lab₀ a =
        pathWord φ lab₀ (φ a) (per φ a - 1) * pathWord φ lab₀ (φ b) (per φ b - 1) ∧
      faceWord φ lab a = pathWord φ lab₀ (φ a) (per φ a - 1) * lab a ∧
      faceWord φ lab b = pathWord φ lab₀ (φ b) (per φ b - 1) * lab b := by
  set ψ := φ * swap a b
  set m := per φ a
  set n := per φ b
  have hm := per_pos φ a
  have hn := per_pos φ b
  have hab' : a ≠ b := fun h ↦ hab (h ▸ Perm.SameCycle.refl _ _)
  -- iterates from `φ b`, resp. `φ a`
  have hbA : ∀ i < n - 1, (φ ^ i) (φ b) ≠ a ∧ (φ ^ i) (φ b) ≠ b := fun i hi ↦ by
    rw [← Perm.mul_apply, ← pow_succ]
    exact ⟨fun h ↦ hab (h ▸ sameCycle_pow _).symm, pow_ne_self (by omega) (by omega)⟩
  have haB : ∀ i < m - 1, (φ ^ i) (φ a) ≠ a ∧ (φ ^ i) (φ a) ≠ b := fun i hi ↦ by
    rw [← Perm.mul_apply, ← pow_succ]
    exact ⟨pow_ne_self (by omega) (by omega), fun h ↦ hab (h ▸ sameCycle_pow _)⟩
  have hA : ∀ i ≤ n - 1, (ψ ^ (i + 1)) a = (φ ^ (i + 1)) b := fun i hi ↦ by
    rw [pow_succ, Perm.mul_apply, mul_swap_apply_left, pow_mul_swap_eq φ hbA i hi,
      ← Perm.mul_apply, ← pow_succ]
  have hB : ∀ i ≤ m - 1, (ψ ^ (i + 1)) b = (φ ^ (i + 1)) a := fun i hi ↦ by
    rw [pow_succ, Perm.mul_apply, mul_swap_apply_right, pow_mul_swap_eq φ haB i hi,
      ← Perm.mul_apply, ← pow_succ]
  have hna : (ψ ^ n) a = b := by
    have := hA (n - 1) le_rfl
    rwa [show n - 1 + 1 = n by omega, pow_per] at this
  have hC : ∀ i ≤ m - 1, (ψ ^ (n + (i + 1))) a = (φ ^ (i + 1)) a := fun i hi ↦ by
    rw [add_comm, pow_add, Perm.mul_apply, hna, hB i hi]
  refine ⟨fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := hx.exists_nat_pow_eq
    clear hx
    induction k with
    | zero => exact Or.inl (Perm.SameCycle.refl _ _)
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply]
      by_cases hya : (ψ ^ k) a = a
      · rw [hya, mul_swap_apply_left]
        exact Or.inr (Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _))
      by_cases hyb : (ψ ^ k) a = b
      · rw [hyb, mul_swap_apply_right]
        exact Or.inl (Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _))
      rw [mul_swap_apply_of_ne φ hya hyb]
      rcases ih with h | h
      · exact Or.inl (Perm.sameCycle_apply_right.2 h)
      · exact Or.inr (Perm.sameCycle_apply_right.2 h)
  · rcases hx with hx | hx
    · obtain ⟨i, him, rfl⟩ := exists_lt_per hx
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact Perm.SameCycle.refl _ _
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [← hC i' (by omega)]; exact sameCycle_pow _
    · obtain ⟨i, him, rfl⟩ := exists_lt_per hx
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [pow_zero, Perm.one_apply, ← hna]; exact sameCycle_pow _
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [← hA i' (by omega)]; exact sameCycle_pow _
  · have hper : per ψ a = n + m := by
      refine per_eq (by omega) ?_ fun k hk hk' ↦ ?_
      · have := hC (m - 1) le_rfl
        rwa [show m - 1 + 1 = m by omega, pow_per] at this
      · rcases Nat.lt_or_ge n k with hnk | hnk
        · obtain ⟨i, rfl⟩ : ∃ i, k = n + (i + 1) := ⟨k - n - 1, by omega⟩
          rw [hC i (by omega)]; exact pow_ne_self (by omega) (by omega)
        · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
          rw [hA i (by omega)]
          exact fun h ↦ hab (h ▸ sameCycle_pow _).symm
    have hw1 : pathWord ψ lab₀ a n = pathWord φ lab₀ (φ b) (n - 1) := by
      have h := pathWord_add ψ lab₀ a 1 (n - 1)
      rw [show 1 + (n - 1) = n by omega, pow_one, pathWord_one, mul_swap_apply_left, hla,
        mul_one] at h
      rw [h]
      refine pathWord_congr' fun i hi ↦ ?_
      rw [pow_mul_swap_eq φ hbA i hi.le]
    have hw2 : pathWord ψ lab₀ b m = pathWord φ lab₀ (φ a) (m - 1) := by
      have h := pathWord_add ψ lab₀ b 1 (m - 1)
      rw [show 1 + (m - 1) = m by omega, pow_one, pathWord_one, mul_swap_apply_right, hlb,
        mul_one] at h
      rw [h]
      refine pathWord_congr' fun i hi ↦ ?_
      rw [pow_mul_swap_eq φ haB i hi.le]
    rw [faceWord, hper, pathWord_add, hna, hw1, hw2]
  · rw [faceWord_eq_pathWord_succ]
    congr 1
    exact pathWord_congr' fun i hi ↦ (hl _ (haB i hi).1 (haB i hi).2).symm
  · rw [faceWord_eq_pathWord_succ]
    congr 1
    exact pathWord_congr' fun i hi ↦ (hl _ (hbA i hi).1 (hbA i hi).2).symm

/-- **Splitting** a cycle: if `a ≠ b` lie on one cycle of `φ`, then in `φ * swap a b` the cycle
splits into the cycle of `a` (the arc after `b`) and the cycle of `b` (the arc after `a`); the
words (with the letters at `a`, `b` erased) are the two arcs. -/
lemma split {lab lab₀ : D → G} (hab : φ.SameCycle a b) (hab' : a ≠ b) (hla : lab₀ a = 1)
    (hlb : lab₀ b = 1) (hl : ∀ y, y ≠ a → y ≠ b → lab₀ y = lab y) :
    ∃ j, 0 < j ∧ j < per φ a ∧ ¬ (φ * swap a b).SameCycle a b ∧
      (∀ x, (φ * swap a b).SameCycle a x → φ.SameCycle a x) ∧
      (∀ x, (φ * swap a b).SameCycle b x → φ.SameCycle a x) ∧
      (∀ x, φ.SameCycle a x → (φ * swap a b).SameCycle a x ∨ (φ * swap a b).SameCycle b x) ∧
      faceWord (φ * swap a b) lab₀ a = pathWord φ lab₀ (φ b) (per φ a - j - 1) ∧
      faceWord (φ * swap a b) lab₀ b = pathWord φ lab₀ (φ a) (j - 1) ∧
      faceWord φ lab a = pathWord φ lab₀ (φ b) (per φ a - j - 1) * lab b *
        (pathWord φ lab₀ (φ a) (j - 1) * lab a) := by
  set ψ := φ * swap a b
  set m := per φ a
  obtain ⟨j, hjm, hj⟩ := exists_lt_per hab
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact absurd hj hab'
    · exact h
  have hidx : ∀ i, j < i → i < m → (φ ^ i) a ≠ a ∧ (φ ^ i) a ≠ b := fun i hi hi' ↦
    ⟨pow_ne_self (by omega) hi', fun h ↦ by
      have := pow_inj hi' hjm (h.trans hj.symm); omega⟩
  have hidx' : ∀ i, 0 < i → i < j → (φ ^ i) a ≠ a ∧ (φ ^ i) a ≠ b := fun i hi hi' ↦
    ⟨pow_ne_self hi (by omega), fun h ↦ by
      have := pow_inj (by omega) hjm (h.trans hj.symm); omega⟩
  have hφb : ∀ i, (φ ^ i) (φ b) = (φ ^ (j + 1 + i)) a := fun i ↦ by
    rw [← hj, ← Perm.mul_apply φ (φ ^ j), ← pow_succ', ← Perm.mul_apply (φ ^ i), ← pow_add]
    congr 2; omega
  have hφa : ∀ i, (φ ^ i) (φ a) = (φ ^ (i + 1)) a := fun i ↦ by
    rw [← Perm.mul_apply, ← pow_succ]
  have hbA : ∀ i < m - j - 1, (φ ^ i) (φ b) ≠ a ∧ (φ ^ i) (φ b) ≠ b := fun i hi ↦ by
    rw [hφb]; exact hidx _ (by omega) (by omega)
  have haB : ∀ i < j - 1, (φ ^ i) (φ a) ≠ a ∧ (φ ^ i) (φ a) ≠ b := fun i hi ↦ by
    rw [hφa]; exact hidx' _ (by omega) (by omega)
  have hA : ∀ i ≤ m - j - 1, (ψ ^ (i + 1)) a = (φ ^ (j + 1 + i)) a := fun i hi ↦ by
    rw [pow_succ, Perm.mul_apply, mul_swap_apply_left, pow_mul_swap_eq φ hbA i hi, hφb]
  have hB : ∀ i ≤ j - 1, (ψ ^ (i + 1)) b = (φ ^ (i + 1)) a := fun i hi ↦ by
    rw [pow_succ, Perm.mul_apply, mul_swap_apply_right, pow_mul_swap_eq φ haB i hi, hφa]
  have hm := per_pos φ a
  have hperA : per ψ a = m - j := by
    refine per_eq (by omega) ?_ fun k hk hk' ↦ ?_
    · have := hA (m - j - 1) le_rfl
      rwa [show m - j - 1 + 1 = m - j by omega, show j + 1 + (m - j - 1) = m by omega,
        pow_per] at this
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      rw [hA i (by omega)]; exact (hidx _ (by omega) (by omega)).1
  have hperB : per ψ b = j := by
    refine per_eq hj0 ?_ fun k hk hk' ↦ ?_
    · have := hB (j - 1) le_rfl
      rwa [show j - 1 + 1 = j by omega, hj] at this
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      rw [hB i (by omega)]; exact (hidx' _ (by omega) (by omega)).2
  have horbA : ∀ x, ψ.SameCycle a x → x = a ∨ ∃ i, j < i ∧ i < m ∧ x = (φ ^ i) a := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := exists_lt_per hx
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Or.inl rfl
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      exact Or.inr ⟨j + 1 + i, by omega, by omega, hA i (by omega)⟩
  refine ⟨j, hj0, hjm, fun h ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, ?_, ?_, ?_⟩
  · rcases horbA b h with h' | ⟨i, hi, hi', h'⟩
    · exact hab' h'.symm
    · exact (hidx i hi hi').2 h'.symm
  · rcases horbA x hx with rfl | ⟨i, -, -, rfl⟩
    · exact Perm.SameCycle.refl _ _
    · exact sameCycle_pow _
  · obtain ⟨k, hk, rfl⟩ := exists_lt_per hx
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact hab
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      rw [hB i (by omega)]; exact sameCycle_pow _
  · obtain ⟨i, him, rfl⟩ := exists_lt_per hx
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Or.inl (Perm.SameCycle.refl _ _)
    rcases Nat.lt_or_ge j i with hji | hji
    · left
      obtain ⟨i', rfl⟩ : ∃ i', i = j + 1 + i' := ⟨i - j - 1, by omega⟩
      rw [← hA i' (by omega)]; exact sameCycle_pow _
    · right
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [← hB i' (by omega)]; exact sameCycle_pow _
  · have h := pathWord_add ψ lab₀ a 1 (m - j - 1)
    rw [show 1 + (m - j - 1) = m - j by omega, pow_one, pathWord_one, mul_swap_apply_left, hla,
      mul_one] at h
    rw [faceWord, hperA, h]
    refine pathWord_congr' fun i hi ↦ ?_
    rw [pow_mul_swap_eq φ hbA i hi.le]
  · have h := pathWord_add ψ lab₀ b 1 (j - 1)
    rw [show 1 + (j - 1) = j by omega, pow_one, pathWord_one, mul_swap_apply_right, hlb,
      mul_one] at h
    rw [faceWord, hperB, h]
    refine pathWord_congr' fun i hi ↦ ?_
    rw [pow_mul_swap_eq φ haB i hi.le]
  · have h1 := pathWord_add φ lab a j (1 + (m - j - 1))
    have h2 := pathWord_add φ lab b 1 (m - j - 1)
    have h3 := pathWord_add φ lab a 1 (j - 1)
    rw [show j + (1 + (m - j - 1)) = m by omega, hj, h2] at h1
    rw [show 1 + (j - 1) = j by omega] at h3
    have e1 : pathWord φ lab (φ b) (m - j - 1) = pathWord φ lab₀ (φ b) (m - j - 1) :=
      pathWord_congr' fun i hi ↦ (hl _ (hbA i hi).1 (hbA i hi).2).symm
    have e2 : pathWord φ lab (φ a) (j - 1) = pathWord φ lab₀ (φ a) (j - 1) :=
      pathWord_congr' fun i hi ↦ (hl _ (haB i hi).1 (haB i hi).2).symm
    simp only [pow_one] at h1 h3
    rw [faceWord, h1, h3, e1, e2, pathWord_one, pathWord_one]

end Swap

end Pi1.Ribbon
