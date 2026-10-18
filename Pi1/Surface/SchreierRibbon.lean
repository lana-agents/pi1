/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.RibbonGraph
public import Pi1.Surface.SchreierCusps
public import Pi1.Surface.CuspPerm
public import Mathlib.Data.ZMod.Defs

/-!
# The ribbon graph of a finite `F(x₀, …, xₙ)`-set and filling cusps

Let `F = F(x₀, …, xₙ)` act transitively on a finite set `Ω`; put `x_∞ = (x₀ x₁ ⋯ xₙ)⁻¹`. This is
the monodromy of a finite covering `Y → ℙ¹ ∖ {a₀, …, aₙ, ∞}` when `xᵢ` is a loop around `aᵢ`
and the `xᵢ` are ordered so that `x₀ ⋯ xₙ x_∞ = 1`. The covering retracts onto the *Schreier
graph*: vertices `Ω`, one edge `ω → xₐ ω` for each `(ω, a)`; the cyclic order `x₀, x₁, …, xₙ` of
the loops at the base point makes it a ribbon graph (`SchreierRibbon.ribbon`). Its darts are
`Ω × Fin (n + 1) × Bool` (`(ω, a, true)` leaves `ω` along `xₐ`, `(ω, a, false)` arrives at `ω`
along `xₐ`), and its faces are

* the `⟨xₐ⟩`-orbits (the darts `(ω, a, true)`): the punctures of `Y` over `aₐ`;
* the `⟨x_∞⟩`-orbits (the darts `(ω, a, false)`): the punctures of `Y` over `∞`.

With the Schreier transversal of a breadth-first search as spanning tree, the face words are the
Reidemeister rewritings of the cusp loops `t ω⁻¹ xₐ^m t ω` and `t ω⁻¹ x_∞^m t ω`
(`faceWord_true`, `faceWord_false`). The surface normal form for ribbon graphs
(`Pi1.Ribbon.RibbonData.isGeom`) then gives a geometric basis of the stabiliser `H` of `ω₀`, and
filling in the punctures over the `aₐ`
(`Pi1.SurfaceGroup.exists_quotient_normalClosure_cusp_mulEquiv`):

**Theorem** (`exists_quotient_cuspSubgroup_mulEquiv_surfaceGroup`).
`H ⧸ cuspSubgroup univ ω₀ ≃* Π_{g,r}` where `r` is the number of `⟨x_∞⟩`-orbits, the cusp of the
orbit of `ω` being sent to a conjugate of `cⱼ` (for the `⟨x_∞⟩`-orbit `j` of `ω`), and
`2g + r + ∑ₐ #(⟨xₐ⟩-orbits) + |Ω| = |Ω| (n + 1) + 2` (Riemann–Hurwitz).

Topologically, `H ⧸ cuspSubgroup univ ω₀` is `π₁` of the curve obtained from `Y` by filling in
the punctures over `a₀, …, aₙ`, and the theorem says that the loops around the remaining
punctures (over `∞`) are, up to conjugacy, the cusp generators of a standard presentation. The
permutation description of ribbon graphs (combinatorial maps) used here is classical; see for
instance Lando–Zvonkin, *Graphs on Surfaces and Their Applications*, Ch. 1 "Constellations,
Coverings, and Maps".
-/

@[expose] public section

namespace Pi1.ReidemeisterSchreier

open FreeGroup Equiv Function

universe v

variable {n : ℕ}

/-- The loop around `∞`: `x_∞ = (x₀ x₁ ⋯ xₙ)⁻¹`. -/
def xInf (n : ℕ) : FreeGroup (Fin (n + 1)) := (List.ofFn fun a : Fin (n + 1) ↦ of a).prod⁻¹

/-! ### Powers inside a finite set -/

section Powers

variable {G Ω : Type*} [Group G] [MulAction G Ω]

lemma mk_eq_mk_zpowers_iff (x : G) {ω ω' : Ω} :
    (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers x) Ω) ω =
      Quotient.mk (MulAction.orbitRel (Subgroup.zpowers x) Ω) ω') ↔ ∃ k : ℤ, x ^ k • ω' = ω := by
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨_, Subgroup.zpow_mem_zpowers _ k⟩, rfl⟩

lemma exists_zpow_iff_exists_pow [Finite Ω] (x : G) {ω ω' : Ω} :
    (∃ k : ℤ, x ^ k • ω = ω') ↔ ∃ k : ℕ, x ^ k • ω = ω' := by
  constructor
  · rintro ⟨k, rfl⟩
    have hp : 0 < minimalPeriod (x • ·) ω :=
      minimalPeriod_pos_of_mem_periodicPts ((MulAction.injective x).mem_periodicPts ω)
    refine ⟨(k % (minimalPeriod (x • ·) ω : ℤ)).toNat, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)),
      MulAction.zpow_smul_mod_minimalPeriod]
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [zpow_natCast]⟩

end Powers

namespace SchreierRibbon

open Fin.NatCast Fin.CommRing

variable {Ω : Type v} [MulAction (FreeGroup (Fin (n + 1))) Ω]

/-- The rotation of the Schreier ribbon graph: at each vertex the darts are ordered
`(ω, 0, false), (ω, 0, true), (ω, 1, false), …, (ω, n, true)`. -/
def rot : Perm (Ω × Fin (n + 1) × Bool) where
  toFun x := if x.2.2 then (x.1, x.2.1 + 1, false) else (x.1, x.2.1, true)
  invFun x := if x.2.2 then (x.1, x.2.1, false) else (x.1, x.2.1 - 1, true)
  left_inv := by rintro ⟨ω, a, _ | _⟩ <;> simp
  right_inv := by rintro ⟨ω, a, _ | _⟩ <;> simp

omit [MulAction (FreeGroup (Fin (n + 1))) Ω] in
@[simp] lemma rot_false (ω : Ω) (a : Fin (n + 1)) : rot (ω, a, false) = (ω, a, true) := by
  simp [rot]

omit [MulAction (FreeGroup (Fin (n + 1))) Ω] in
@[simp] lemma rot_true (ω : Ω) (a : Fin (n + 1)) : rot (ω, a, true) = (ω, a + 1, false) := by
  simp [rot]

/-- The edge involution of the Schreier ribbon graph. -/
def edge : Perm (Ω × Fin (n + 1) × Bool) where
  toFun x := if x.2.2 then (of x.2.1 • x.1, x.2.1, false) else ((of x.2.1)⁻¹ • x.1, x.2.1, true)
  invFun x := if x.2.2 then (of x.2.1 • x.1, x.2.1, false) else ((of x.2.1)⁻¹ • x.1, x.2.1, true)
  left_inv := by rintro ⟨ω, a, _ | _⟩ <;> simp
  right_inv := by rintro ⟨ω, a, _ | _⟩ <;> simp

@[simp] lemma edge_true (ω : Ω) (a : Fin (n + 1)) : edge (ω, a, true) = (of a • ω, a, false) := by
  simp [edge]

@[simp] lemma edge_false (ω : Ω) (a : Fin (n + 1)) :
    edge (ω, a, false) = ((of a)⁻¹ • ω, a, true) := by
  simp [edge]

omit [MulAction (FreeGroup (Fin (n + 1))) Ω] in
lemma sameCycle_rot_zero (x : Ω × Fin (n + 1) × Bool) : rot.SameCycle (x.1, 0, false) x := by
  obtain ⟨ω, a, b⟩ := x
  have hf : ∀ a : Fin (n + 1), rot.SameCycle ((ω, 0, false) : Ω × Fin (n + 1) × Bool)
      (ω, a, false) := by
    intro a
    induction a using Fin.induction with
    | zero => exact Perm.SameCycle.refl _ _
    | succ i ih =>
      have h := (Perm.sameCycle_apply_right.2 (Perm.sameCycle_apply_right.2 ih))
      rwa [rot_false, rot_true, Fin.coeSucc_eq_succ] at h
  cases b with
  | false => exact hf a
  | true =>
    have h := Perm.sameCycle_apply_right.2 (hf a)
    rwa [rot_false] at h

omit [MulAction (FreeGroup (Fin (n + 1))) Ω] in
lemma sameCycle_rot {x y : Ω × Fin (n + 1) × Bool} (h : x.1 = y.1) : rot.SameCycle x y := by
  have := sameCycle_rot_zero y
  rw [← h] at this
  exact (sameCycle_rot_zero x).symm.trans this

variable [DecidableEq Ω] {ω₀ : Ω} (T : Transversal (Fin (n + 1)) ω₀)

open scoped Classical in
/-- The label of a dart on the edge `e`: `none` on tree edges. -/
noncomputable def ltE (e : Ω × Fin (n + 1)) (b : Bool) : Option (T.Gens × Bool) :=
  if h : e ∈ T.E then none else some (⟨e, h⟩, b)

omit [DecidableEq Ω] in
lemma ltE_of_mem {e : Ω × Fin (n + 1)} (h : e ∈ T.E) (b : Bool) : (ltE T) e b = none := by
  simp [ltE, h]

omit [DecidableEq Ω] in
lemma ltE_of_notMem {e : Ω × Fin (n + 1)} (h : e ∉ T.E) (b : Bool) :
    (ltE T) e b = some (⟨e, h⟩, b) := by
  simp [ltE, h]

omit [DecidableEq Ω] in
lemma ltE_eq_none_iff {e : Ω × Fin (n + 1)} {b : Bool} : (ltE T) e b = none ↔ e ∈ T.E := by
  by_cases h : e ∈ T.E <;> simp [ltE, h]

omit [DecidableEq Ω] in
lemma ltE_map (e : Ω × Fin (n + 1)) (b : Bool) :
    ((ltE T) e b).map (fun p ↦ (p.1, !p.2)) = (ltE T) e (!b) := by
  by_cases h : e ∈ T.E <;> simp [ltE, h]

/-- The labels of the darts: the dart `(ω, a, true)` lies on the edge `(ω, a)`, the dart
`(ω, a, false)` on the edge `(xₐ⁻¹ ω, a)`. -/
noncomputable def ltD (x : Ω × Fin (n + 1) × Bool) : Option (T.Gens × Bool) :=
  if x.2.2 then (ltE T) (x.1, x.2.1) true else (ltE T) ((of x.2.1)⁻¹ • x.1, x.2.1) false

omit [DecidableEq Ω] in
@[simp] lemma ltD_true (ω : Ω) (a : Fin (n + 1)) : (ltD T) (ω, a, true) = (ltE T) (ω, a) true := by
  simp [ltD]

omit [DecidableEq Ω] in
@[simp] lemma ltD_false (ω : Ω) (a : Fin (n + 1)) :
    (ltD T) (ω, a, false) = (ltE T) ((of a)⁻¹ • ω, a) false := by
  simp [ltD]

/-- The labels used for the potential of the spanning tree. -/
noncomputable def labT (ω : Ω) (a : Fin (n + 1)) : Multiplicative (Ω × Fin (n + 1) × Bool → ℤ) :=
  Multiplicative.ofAdd (Pi.single (ω, a, true) 1 - Pi.single (of a • ω, a, false) 1)

/-- The potential of a vertex. -/
noncomputable def potV (ω : Ω) : Ω × Fin (n + 1) × Bool → ℤ :=
  Multiplicative.toAdd (coc labT (T.t ω) ω₀)

lemma potV_tree {ω : Ω} {a : Fin (n + 1)} (he : (ω, a) ∈ T.E) (z : Ω × Fin (n + 1) × Bool) :
    (potV T) (of a • ω) z = (potV T) ω z + (if z = (ω, a, true) then 1 else 0) -
      (if z = (of a • ω, a, false) then 1 else 0) := by
  have ht := T.t_mul_eq (e := (ω, a)) he
  simp only at ht
  rw [potV, ht, coc_mul, T.t_smul, coc_of, toAdd_mul, potV, labT, toAdd_ofAdd]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  ring

lemma depth_eq_zero {ω : Ω} (h : T.depth ω = 0) : ω = ω₀ := by
  by_contra hω
  obtain ⟨e, -, h1 | h1⟩ := T.exists_edge ω hω <;> omega

/-- The depth used for the ribbon graph (`0` at the base point). -/
noncomputable def dp (ω : Ω) : ℕ := if ω = ω₀ then 0 else T.depth ω

lemma dp_eq_zero {ω : Ω} (h : (dp T) ω = 0) : ω = ω₀ := by
  unfold dp at h
  split_ifs at h with hω
  · exact hω
  · exact (depth_eq_zero T) h

lemma dp_lt {ω ω' : Ω} (hω : ω ≠ ω₀) (h : T.depth ω' < T.depth ω) : (dp T) ω' < (dp T) ω := by
  unfold dp
  rw [if_neg hω]
  split_ifs with h'
  · exact Nat.pos_of_ne_zero fun h0 ↦ hω ((depth_eq_zero T) h0)
  · exact h

/-- **The Schreier ribbon graph** of the transversal `T`. -/
noncomputable def ribbon : Ribbon.RibbonData (Ω × Fin (n + 1) × Bool) T.Gens where
  σ := rot
  ι := edge
  ι_ι := by rintro ⟨ω, a, _ | _⟩ <;> simp
  ι_ne := by rintro ⟨ω, a, _ | _⟩ <;> simp
  lt := (ltD T)
  lt_ι := by
    rintro ⟨ω, a, _ | _⟩
    · rw [edge_false, ltD_true, ltD_false, ltE_map]; rfl
    · rw [edge_true, ltD_true, ltD_false, inv_smul_smul, ltE_map]; rfl
  lt_unique := by
    rintro ⟨⟨ω, a⟩, he⟩
    refine ⟨(ω, a, true), by simp [ltE_of_notMem T he], ?_⟩
    rintro ⟨ω', a', _ | _⟩ h
    · simp only [ltD_false, ltE] at h
      split_ifs at h
      simp at h
    · simp only [ltD_true, ltE] at h
      split_ifs at h with h'
      simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq, and_true] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  pot x z := (potV T) x.1 z
  pot_σ := by rintro ⟨ω, a, _ | _⟩ <;> simp
  pot_ι := by
    rintro ⟨ω, a, _ | _⟩ hx z
    · simp only [ltD_false, ltE_eq_none_iff] at hx
      simp only [edge_false]
      have h := (potV_tree T) hx z
      rw [smul_inv_smul] at h
      rw [h]
      ring
    · simp only [ltD_true, ltE_eq_none_iff] at hx
      simp only [edge_true]
      exact (potV_tree T) hx z
  dep x := (dp T) x.1
  dep_σ := by rintro ⟨ω, a, _ | _⟩ <;> simp
  root x y hx hy := sameCycle_rot (((dp_eq_zero T) hx).trans ((dp_eq_zero T) hy).symm)
  parent := by
    rintro ⟨ω, a, b⟩ hx
    have hω : ω ≠ ω₀ := by
      rintro rfl
      simp [dp] at hx
    obtain ⟨⟨ω', c⟩, he, ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩⟩ := T.exists_edge ω hω
    · refine ⟨(ω', c, true), by simp [ltE_of_mem T he], sameCycle_rot rfl, ?_⟩
      simpa using (dp_lt T) hω hlt
    · refine ⟨(of c • ω', c, false), by simp [ltE_of_mem T he], sameCycle_rot rfl, ?_⟩
      simpa using (dp_lt T) hω hlt

lemma ribbon_φ_true (ω : Ω) (a : Fin (n + 1)) :
    (ribbon T).φ (ω, a, true) = (of a • ω, a, true) := by
  simp [Ribbon.RibbonData.φ_apply, ribbon]

lemma ribbon_φ_false (ω : Ω) (a : Fin (n + 1)) :
    (ribbon T).φ (ω, a, false) = ((of a)⁻¹ • ω, a + 1, false) := by
  simp [Ribbon.RibbonData.φ_apply, ribbon]

lemma ribbon_lab_true (ω : Ω) (a : Fin (n + 1)) : (ribbon T).lab (ω, a, true) = T.lab ω a := by
  by_cases h : (ω, a) ∈ T.E
  · simp [Ribbon.RibbonData.lab, ribbon, ltE_of_mem T h, Ribbon.labOf, T.lab_of_mem h]
  · simp [Ribbon.RibbonData.lab, ribbon, ltE_of_notMem T h, Ribbon.labOf,
      T.lab_of_notMem ⟨(ω, a), h⟩]

lemma ribbon_lab_false (ω : Ω) (a : Fin (n + 1)) :
    (ribbon T).lab (ω, a, false) = (T.lab ((of a)⁻¹ • ω) a)⁻¹ := by
  by_cases h : ((of a)⁻¹ • ω, a) ∈ T.E
  · simp [Ribbon.RibbonData.lab, ribbon, ltE_of_mem T h, Ribbon.labOf, T.lab_of_mem h]
  · simp [Ribbon.RibbonData.lab, ribbon, ltE_of_notMem T h, Ribbon.labOf,
      T.lab_of_notMem ⟨((of a)⁻¹ • ω, a), h⟩]

/-! ### The faces over the `aₐ` -/

lemma ribbon_φ_pow_true (ω : Ω) (a : Fin (n + 1)) (k : ℕ) :
    ((ribbon T).φ ^ k) (ω, a, true) = ((of a) ^ k • ω, a, true) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Perm.mul_apply, ih, ribbon_φ_true, ← mul_smul, ← pow_succ']

lemma ribbon_pathWord_true (ω : Ω) (a : Fin (n + 1)) (k : ℕ) :
    Ribbon.pathWord (ribbon T).φ (ribbon T).lab (ω, a, true) k = coc T.lab ((of a) ^ k) ω := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Ribbon.pathWord_succ, ih, ribbon_φ_pow_true, ribbon_lab_true, pow_succ', coc_mul, coc_of]

lemma ribbon_per_true (ω : Ω) (a : Fin (n + 1)) :
    Ribbon.per (ribbon T).φ (ω, a, true) = per a ω := by
  refine minimalPeriod_eq_minimalPeriod_iff.2 fun k ↦ ?_
  simp only [IsPeriodicPt, IsFixedPt, ← Perm.coe_pow, ribbon_φ_pow_true, smul_iterate,
    Prod.mk.injEq, and_true]

lemma ribbon_faceWord_true [Finite Ω] (ω : Ω) (a : Fin (n + 1)) :
    Ribbon.faceWord (ribbon T).φ (ribbon T).lab (ω, a, true) = coc T.lab ((of a) ^ per a ω) ω := by
  rw [Ribbon.faceWord, ribbon_per_true, ribbon_pathWord_true]

/-! ### The faces over `∞` -/

/-- `w a j = x_{a+j-1}⁻¹ ⋯ x_{a+1}⁻¹ x_a⁻¹`. -/
def wInf (a : Fin (n + 1)) : ℕ → FreeGroup (Fin (n + 1))
  | 0 => 1
  | j + 1 => (of (a + (j : Fin (n + 1))))⁻¹ * wInf a j

lemma wInf_add (a : Fin (n + 1)) (i j : ℕ) :
    wInf a (i + j) = wInf (a + (i : Fin (n + 1))) j * wInf a i := by
  induction j with
  | zero => simp [wInf]
  | succ j ih =>
    rw [← add_assoc]
    simp only [wInf]
    rw [ih, Nat.cast_add, add_assoc, mul_assoc]

lemma wInf_zero_eq (j : ℕ) :
    wInf (0 : Fin (n + 1)) j = (List.ofFn fun i : Fin j ↦ of ((i : ℕ) : Fin (n + 1))).prod⁻¹ := by
  induction j with
  | zero => simp [wInf]
  | succ j ih =>
    rw [wInf, ih, List.ofFn_succ', List.prod_concat, mul_inv_rev, zero_add]
    simp

lemma wInf_zero_succ : wInf (0 : Fin (n + 1)) (n + 1) = xInf n := by
  rw [wInf_zero_eq, xInf]
  simp [Fin.cast_val_eq_self]

lemma wInf_zero_mul (k : ℕ) : wInf (0 : Fin (n + 1)) ((n + 1) * k) = xInf n ^ k := by
  induction k with
  | zero => simp [wInf]
  | succ k ih =>
    rw [Nat.mul_succ, wInf_add, ih, Nat.cast_mul, Fin.natCast_self (n + 1), zero_mul, add_zero,
      wInf_zero_succ, pow_succ']

variable {T} in
lemma ribbon_φ_pow_false (ω : Ω) (a : Fin (n + 1)) (j : ℕ) :
    ((ribbon T).φ ^ j) (ω, a, false) = (wInf a j • ω, a + (j : Fin (n + 1)), false) := by
  induction j with
  | zero => simp [wInf]
  | succ j ih =>
    rw [pow_succ', Perm.mul_apply, ih, ribbon_φ_false, wInf, mul_smul, Nat.cast_succ, add_assoc]

omit [DecidableEq Ω] in
lemma coc_of_inv {G : Type*} [Group G] (lab : Ω → Fin (n + 1) → G) (b : Fin (n + 1)) (y : Ω) :
    coc lab (of b)⁻¹ y = (lab ((of b)⁻¹ • y) b)⁻¹ := by
  have h := coc_inv lab (of b) ((of b)⁻¹ • y)
  rwa [smul_inv_smul, coc_of] at h

lemma ribbon_pathWord_false (ω : Ω) (a : Fin (n + 1)) (j : ℕ) :
    Ribbon.pathWord (ribbon T).φ (ribbon T).lab (ω, a, false) j = coc T.lab (wInf a j) ω := by
  induction j with
  | zero => simp [wInf]
  | succ j ih =>
    rw [Ribbon.pathWord_succ, ih, ribbon_φ_pow_false, ribbon_lab_false, wInf, coc_mul,
      coc_of_inv]

lemma ribbon_φ_pow_false_mul (ω : Ω) (k : ℕ) :
    ((ribbon T).φ ^ ((n + 1) * k)) (ω, 0, false) = (xInf n ^ k • ω, 0, false) := by
  rw [ribbon_φ_pow_false, wInf_zero_mul, Nat.cast_mul, Fin.natCast_self (n + 1), zero_mul,
    add_zero]

lemma ribbon_φ_pow_false_eq_iff (ω ω' : Ω) (j : ℕ) :
    ((ribbon T).φ ^ j) (ω, 0, false) = (ω', 0, false) ↔
      ∃ k, j = (n + 1) * k ∧ xInf n ^ k • ω = ω' := by
  constructor
  · intro h
    have h' := h
    rw [ribbon_φ_pow_false] at h'
    have h2 : ((j : ℕ) : Fin (n + 1)) = 0 := by simpa using congrArg (fun x ↦ x.2.1) h'
    obtain ⟨k, rfl⟩ := (Fin.natCast_eq_zero (n := n + 1)).1 h2
    refine ⟨k, rfl, ?_⟩
    rw [ribbon_φ_pow_false_mul] at h
    exact congrArg Prod.fst h
  · rintro ⟨k, rfl, rfl⟩
    exact ribbon_φ_pow_false_mul T ω k

variable (n) in
/-- The period of `x_∞` at `ω`. -/
noncomputable abbrev perInf (ω : Ω) : ℕ := minimalPeriod (xInf n • ·) ω

lemma ribbon_per_false [Finite Ω] (ω : Ω) :
    Ribbon.per (ribbon T).φ (ω, 0, false) = (n + 1) * perInf n ω := by
  have hper : ∀ j, IsPeriodicPt (ribbon T).φ j (ω, 0, false) ↔
      ∃ k, j = (n + 1) * k ∧ xInf n ^ k • ω = ω := fun j ↦ by
    rw [IsPeriodicPt, IsFixedPt, ← Perm.coe_pow, ribbon_φ_pow_false_eq_iff]
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    exact (hper _).2 ⟨_, rfl, (MulAction.pow_smul_eq_iff_minimalPeriod_dvd (a := xInf n)
      (b := ω)).2 dvd_rfl⟩
  · obtain ⟨k, hk, hk'⟩ := (hper _).1 (isPeriodicPt_minimalPeriod (ribbon T).φ (ω, 0, false))
    change (n + 1) * perInf n ω ∣ minimalPeriod (ribbon T).φ (ω, 0, false)
    rw [hk]
    exact Nat.mul_dvd_mul_left _ (MulAction.pow_smul_eq_iff_minimalPeriod_dvd.1 hk')

lemma ribbon_faceWord_false [Finite Ω] (ω : Ω) :
    Ribbon.faceWord (ribbon T).φ (ribbon T).lab (ω, 0, false) =
      coc T.lab (xInf n ^ perInf n ω) ω := by
  rw [Ribbon.faceWord, ribbon_per_false, ribbon_pathWord_false, wInf_zero_mul]

/-! ### Cycles of the face permutation -/

section Finite

variable [Finite Ω]

lemma ribbon_sameCycle_true_iff (ω : Ω) (a : Fin (n + 1)) (y : Ω × Fin (n + 1) × Bool) :
    (ribbon T).φ.SameCycle (ω, a, true) y ↔ ∃ k : ℕ, ((of a) ^ k • ω, a, true) = y := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    exact ⟨k, (ribbon_φ_pow_true T ω a k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [zpow_natCast, ribbon_φ_pow_true]⟩

lemma ribbon_sameCycle_false_iff (ω ω' : Ω) :
    (ribbon T).φ.SameCycle (ω, 0, false) (ω', 0, false) ↔ ∃ k : ℕ, xInf n ^ k • ω = ω' := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := h.exists_nat_pow_eq
    obtain ⟨k, -, hk⟩ := (ribbon_φ_pow_false_eq_iff T ω ω' j).1 hj
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨((n + 1) * k : ℕ), by rw [zpow_natCast, ribbon_φ_pow_false_mul, hk]⟩

omit [Finite Ω] in
lemma ribbon_exists_sameCycle_false (ω : Ω) (a : Fin (n + 1)) :
    ∃ ω', (ribbon T).φ.SameCycle (ω, a, false) (ω', 0, false) := by
  refine ⟨wInf a (n + 1 - a) • ω, ⟨((n + 1 - a : ℕ) : ℤ), ?_⟩⟩
  rw [zpow_natCast, ribbon_φ_pow_false]
  congr
  have : ((a : ℕ) : Fin (n + 1)) + ((n + 1 - a : ℕ) : Fin (n + 1)) = 0 := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' a.is_lt.le, Fin.natCast_self (n + 1)]
  rwa [Fin.cast_val_eq_self] at this

lemma ribbon_not_sameCycle_true_false (ω ω' : Ω) (a a' : Fin (n + 1)) :
    ¬ (ribbon T).φ.SameCycle (ω, a, true) (ω', a', false) := by
  rw [ribbon_sameCycle_true_iff]
  rintro ⟨k, h⟩
  simp at h

end Finite

end SchreierRibbon

end Pi1.ReidemeisterSchreier
