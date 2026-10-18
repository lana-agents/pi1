/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.CycleWord
public import Pi1.Surface.SurfaceMoves
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Geometric bases of the fundamental group of a ribbon graph

A *ribbon graph* (fat graph, combinatorial map) is a finite set `D` of darts (half-edges) with an
involution `ι` without fixed points (the edges) and a permutation `σ` (the cyclic order of the
darts around each vertex). Its faces are the cycles of `φ = σ ι`; thickening the graph gives an
oriented surface with boundary whose boundary components are the faces, and gluing discs to
the faces gives a closed oriented surface of genus `g` with `V - E + F = 2 - 2g`
(see e.g. Mohar–Thomassen, *Graphs on Surfaces*, §3.2 "Rotation systems" and §3.3 "Embedding
schemes", or Lando–Zvonkin, *Graphs on Surfaces and Their Applications*, Ch. 1 "Constellations,
Coverings, and Maps", for this permutation description).

We fix a spanning tree and describe `π₁` of the graph as the free group `F(L)` on the non-tree
edges (Reidemeister–Schreier): each dart carries a label `lab x ∈ {1, ℓ, ℓ⁻¹}` (`1` on tree
edges) and a closed walk maps to the product of its labels. The *face word* of a face is the
product of the labels along it (`Pi1.Ribbon.faceWord`).

**Theorem** (`Pi1.Ribbon.RibbonData.isGeom`). `F(L) ≅ Π_{g,R}` for some `g`, where `R` is the
number of faces, such that the cusp `cⱼ` is sent to a conjugate of the face word of the `j`-th
face, and `|L| + 1 = 2g + R`.

This is the classical normal form of a punctured surface: the cusps of the surface obtained by
thickening the ribbon graph are its faces (cf. Massey, *Algebraic Topology: An Introduction*,
Ch. 1, for the classification by cutting and pasting). The proof is by induction on the number
of non-tree edges: deleting a non-tree edge `e` (a non-bridge) either merges the two distinct
faces on its sides (`merge`), which on the group side is `SurfaceGroup.splitCusp`, or splits the
face running along both sides of `e` into two (`split`), which on the group side is
`SurfaceGroup.addHandle`. When only the tree is left there is one face, since its boundary walk
crosses every edge in both directions (a potential argument, `isGeom_of_isEmpty`).

The spanning tree is encoded by two pieces of data: a *potential* `pot` (a vertex function with
`pot (ι x) - pot x = δₓ - δ_{ι x}` on tree darts; it shows that tree edges never separate faces)
and a *depth* function with parent tree darts (connectivity).
-/

@[expose] public section

namespace Pi1.Ribbon

open Equiv FreeGroup SurfaceGroup

variable {L : Type*}

/-- The label of a dart: `1` for tree darts, `ℓ` resp. `ℓ⁻¹` for the two darts of the non-tree
edge `ℓ`. -/
def labOf : Option (L × Bool) → FreeGroup L
  | none => 1
  | some (l, b) => if b then of l else (of l)⁻¹

lemma labOf_flip (o : Option (L × Bool)) :
    labOf (o.map fun p ↦ (p.1, !p.2)) = (labOf o)⁻¹ := by
  rcases o with _ | ⟨l, _ | _⟩ <;> simp [labOf]

/-- A ribbon graph with a spanning tree, see the module docstring. -/
structure RibbonData (D L : Type*) [DecidableEq D] where
  /-- The rotation at the vertices. -/
  σ : Perm D
  /-- The edge involution. -/
  ι : Perm D
  ι_ι : ∀ x, ι (ι x) = x
  ι_ne : ∀ x, ι x ≠ x
  /-- `none` on tree darts, `some (ℓ, true)` resp. `some (ℓ, false)` on the two darts of the
  non-tree edge `ℓ`. -/
  lt : D → Option (L × Bool)
  lt_ι : ∀ x, lt (ι x) = (lt x).map fun p ↦ (p.1, !p.2)
  lt_unique : ∀ l, ∃! x, lt x = some (l, true)
  /-- The potential of the spanning tree. -/
  pot : D → D → ℤ
  pot_σ : ∀ x, pot (σ x) = pot x
  pot_ι : ∀ x, lt x = none → ∀ z,
    pot (ι x) z = pot x z + (if z = x then 1 else 0) - (if z = ι x then 1 else 0)
  /-- The depth in the spanning tree. -/
  dep : D → ℕ
  dep_σ : ∀ x, dep (σ x) = dep x
  root : ∀ x y, dep x = 0 → dep y = 0 → σ.SameCycle x y
  parent : ∀ x, 0 < dep x → ∃ p, lt p = none ∧ σ.SameCycle x p ∧ dep (ι p) < dep x

namespace RibbonData

variable {D : Type*} [DecidableEq D] (G : RibbonData D L)

/-- The face permutation `φ = σ ι`. -/
def φ : Perm D := G.σ * G.ι

lemma φ_apply (x : D) : G.φ x = G.σ (G.ι x) := rfl

lemma σ_eq_φ (x : D) : G.σ x = G.φ (G.ι x) := by rw [φ_apply, G.ι_ι]

/-- The label of a dart. -/
def lab (x : D) : FreeGroup L := labOf (G.lt x)

lemma lab_ι (x : D) : G.lab (G.ι x) = (G.lab x)⁻¹ := by
  simp only [lab, G.lt_ι, labOf_flip]

section Finite

variable [Finite D]

/-- **Geometric basis**: `F(L) ≅ Π_{g,R}` with the cusps going to conjugates of the face words,
one cusp per face. -/
def IsGeom : Prop :=
  ∃ (g R : ℕ) (Ψ : SurfaceGroup g R ≃* FreeGroup L) (ν : D → Fin R),
    Nat.card L + 1 = 2 * g + R ∧ (∀ x y, ν x = ν y ↔ G.φ.SameCycle x y) ∧
      (Nonempty D → Function.Surjective ν) ∧
      ∀ x, IsConj (Ψ (cusp (ν x))) (faceWord G.φ G.lab x)

omit [Finite D] in
lemma eq_or_eq_of_lt {a : D} {e : L} (ha : G.lt a = some (e, true)) {x : D} {c : Bool}
    (hx : G.lt x = some (e, c)) : x = a ∨ x = G.ι a := by
  cases c
  · right
    have h : G.lt (G.ι x) = some (e, true) := by rw [G.lt_ι, hx]; rfl
    have := (G.lt_unique e).unique h ha
    rw [← this, G.ι_ι]
  · left
    exact (G.lt_unique e).unique hx ha

lemma sameCycle_σ_closed {S : D → Prop} (hσ : ∀ y, S y → S (G.σ y)) {x y : D}
    (hxy : G.σ.SameCycle x y) (hx : S x) : S y := by
  obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction k with
  | zero => exact hx
  | succ k ih => rw [pow_succ', Perm.mul_apply]; exact hσ _ ih

/-- **Connectivity**: a set of darts closed under `σ` and `ι` is empty or everything. -/
theorem connected {S : D → Prop} (hσ : ∀ y, S y → S (G.σ y)) (hι : ∀ y, S y → S (G.ι y))
    {x₀ : D} (h₀ : S x₀) (y : D) : S y := by
  have hroot : ∃ r, G.dep r = 0 ∧ S r := by
    induction hd : G.dep x₀ using Nat.strong_induction_on generalizing x₀ with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact ⟨x₀, hd, h₀⟩
      obtain ⟨p, -, hp, hdp⟩ := G.parent x₀ (hd ▸ hn)
      exact ih _ (hd ▸ hdp) (hι _ (G.sameCycle_σ_closed hσ hp h₀)) rfl
  obtain ⟨r, hr, hSr⟩ := hroot
  induction hd : G.dep y using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact G.sameCycle_σ_closed hσ (G.root r y hr hd) hSr
    obtain ⟨p, -, hp, hdp⟩ := G.parent y (hd ▸ hn)
    have h1 : S (G.ι p) := ih _ (hd ▸ hdp) _ rfl
    have h2 : S p := by simpa [G.ι_ι] using hι _ h1
    exact G.sameCycle_σ_closed hσ hp.symm h2

omit [Finite D] in
lemma exists_tree_root (y : D) (hy : 0 < G.dep y) :
    ∃ q, G.lt q = none ∧ G.dep (G.ι q) = 0 := by
  induction hd : G.dep y using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    obtain ⟨p, hp, -, hdp⟩ := G.parent y (hd ▸ hy)
    rcases Nat.eq_zero_or_pos (G.dep (G.ι p)) with h0 | hpos
    · exact ⟨p, hp, h0⟩
    · exact ih _ (hd ▸ hdp) _ hpos rfl

omit [Finite D] in
/-- A non-tree dart is never alone at its vertex (non-tree edges are not bridges). -/
lemma σ_ne_of_lt_ne_none {x : D} (hx : G.lt x ≠ none) : G.σ x ≠ x := by
  intro hfix
  rcases Nat.eq_zero_or_pos (G.dep x) with h0 | hpos
  · have hιx : 0 < G.dep (G.ι x) := by
      rcases Nat.eq_zero_or_pos (G.dep (G.ι x)) with h | h
      · exact absurd ((G.root x _ h0 h).eq_of_left hfix).symm (G.ι_ne x)
      · exact h
    obtain ⟨q, hq, hq0⟩ := G.exists_tree_root _ hιx
    have hxq := (G.root x (G.ι q) h0 hq0).eq_of_left hfix
    have hq' : q = G.ι x := by rw [hxq, G.ι_ι]
    have h := G.lt_ι x
    rw [← hq', hq] at h
    cases hlx : G.lt x with
    | none => exact hx hlx
    | some p => rw [hlx] at h; simp at h
  · obtain ⟨p, hp, hxp, -⟩ := G.parent x hpos
    have := hxp.eq_of_left hfix
    exact hx (this ▸ hp)

/-! ### The tree: one face -/

omit [Finite D] in
lemma pot_pow (htree : ∀ x, G.lt x = none) (x z : D) (n : ℕ) :
    G.pot ((G.φ ^ n) x) z = G.pot x z + ∑ k ∈ Finset.range n,
      ((if z = (G.φ ^ k) x then 1 else 0) - (if z = G.ι ((G.φ ^ k) x) then 1 else 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, φ_apply, G.pot_σ, G.pot_ι _ (htree _), ih,
      Finset.sum_range_succ]
    ring

lemma sameCycle_ι_of_tree (htree : ∀ x, G.lt x = none) {x y : D} (h : G.φ.SameCycle x y) :
    G.φ.SameCycle x (G.ι y) := by
  obtain ⟨j, hj, rfl⟩ := exists_lt_per h
  have hp := G.pot_pow htree x ((G.φ ^ j) x) (per G.φ x)
  rw [pow_per, left_eq_add, Finset.sum_sub_distrib, sub_eq_zero] at hp
  have h1 : (1 : ℤ) ≤ ∑ k ∈ Finset.range (per G.φ x),
      (if (G.φ ^ j) x = (G.φ ^ k) x then (1 : ℤ) else 0) :=
    le_trans (by simp) (Finset.single_le_sum (f := fun k ↦
      if (G.φ ^ j) x = (G.φ ^ k) x then (1 : ℤ) else 0) (fun k _ ↦ by split_ifs <;> simp)
      (Finset.mem_range.2 hj))
  rw [hp] at h1
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero (lt_of_lt_of_le zero_lt_one h1).ne'
  split_ifs at hk with hk'
  · rw [hk', G.ι_ι]; exact sameCycle_pow k
  · exact absurd rfl hk

lemma sameCycle_of_tree (htree : ∀ x, G.lt x = none) (x y : D) : G.φ.SameCycle x y := by
  have hι : ∀ y, G.φ.SameCycle x y → G.φ.SameCycle x (G.ι y) := fun y ↦
    G.sameCycle_ι_of_tree htree
  refine G.connected (S := fun y ↦ G.φ.SameCycle x y) (fun y hy ↦ ?_) hι
    (Perm.SameCycle.refl _ _) y
  rw [σ_eq_φ]
  exact Perm.sameCycle_apply_right.2 (hι y hy)

instance : IsEmpty (SurfaceGen 0 0) := ⟨fun s ↦ by cases s <;> exact Fin.elim0 ‹_›⟩

/-- The base case: a tree has one face. -/
theorem isGeom_of_isEmpty [IsEmpty L] : G.IsGeom := by
  have htree : ∀ x, G.lt x = none := fun x ↦ by
    cases h : G.lt x with
    | none => rfl
    | some p => exact isEmptyElim p.1
  refine ⟨0, 1, freeEquiv.trans (freeGroupCongr (equivOfIsEmpty _ L)), fun _ ↦ 0, ?_,
    fun x y ↦ ⟨fun _ ↦ G.sameCycle_of_tree htree x y, fun _ ↦ rfl⟩,
    fun ⟨x⟩ j ↦ ⟨x, Subsingleton.elim _ _⟩, fun x ↦ isConj_iff.2 ⟨1, Subsingleton.elim _ _⟩⟩
  simp

end Finite

/-! ### Deleting a non-tree edge -/

section Delete

variable [Finite D]

omit [Finite D] in
lemma skip₂_apply_left {π : Perm D} {a b : D} (hab : a ≠ b) : skip (skip π a) b a = a := by
  rw [skip_apply_of_ne hab (by rw [skip_apply_self]; exact hab), skip_apply_self]

omit [Finite D] in
lemma skip₂_live (π : Perm D) {a b : D} (hab : a ≠ b) (x : D) :
    (skip (skip π a) b x ≠ a ∧ skip (skip π a) b x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := by
  have h1 : skip (skip π a) b x = a ↔ x = a := by
    have := (skip (skip π a) b).injective.eq_iff (a := x) (b := a)
    rwa [skip₂_apply_left hab] at this
  have h2 : skip (skip π a) b x = b ↔ x = b := by
    have := (skip (skip π a) b).injective.eq_iff (a := x) (b := b)
    rwa [skip_apply_self] at this
  rw [ne_eq, ne_eq, h1, h2]

omit [Finite D] in
lemma ne_ι (a : D) : a ≠ G.ι a := (G.ι_ne a).symm

/-- The live darts after deleting the edge `{a, ι a}`. -/
abbrev Live (G : RibbonData D L) (a : D) := {x : D // x ≠ a ∧ x ≠ G.ι a}

omit [Finite D] in
lemma ι_live (a x : D) : (G.ι x ≠ a ∧ G.ι x ≠ G.ι a) ↔ (x ≠ a ∧ x ≠ G.ι a) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h ↦ h2 (h ▸ rfl), fun h ↦ h1 (by rw [h, G.ι_ι])⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h ↦ h2 (by rw [← h, G.ι_ι]), fun h ↦ h1 (G.ι.injective h)⟩

variable [DecidableEq L] {a : D} {e : L} (ha : G.lt a = some (e, true))

include ha

omit [DecidableEq L] [Finite D] in
lemma lt_live {x : D} (hx : x ≠ a ∧ x ≠ G.ι a) {p : L × Bool} (hp : G.lt x = some p) :
    p.1 ≠ e := by
  rintro rfl
  rcases G.eq_or_eq_of_lt ha (c := p.2) (by rw [hp]) with h | h
  · exact hx.1 h
  · exact hx.2 h

omit ha [Finite D] in
lemma exists_pow_skip₂ (π : Perm D) (a b x : D) : ∃ k : ℕ, skip (skip π a) b x = (π ^ k) x := by
  obtain ⟨k, hk⟩ := exists_pow_skip (π := skip π a) (h := b) x 1
  obtain ⟨k', hk'⟩ := exists_pow_skip (π := π) (h := a) x k
  exact ⟨k', by rw [← hk', ← hk, pow_one]⟩

/-- The ribbon graph with the non-tree edge `{a, ι a}` deleted. -/
def delete : RibbonData (G.Live a) {l : L // l ≠ e} where
  σ := (skip (skip G.σ a) (G.ι a)).subtypePerm (skip₂_live G.σ (G.ne_ι a))
  ι := G.ι.subtypePerm (G.ι_live a)
  ι_ι x := Subtype.ext (G.ι_ι x.1)
  ι_ne x h := G.ι_ne x.1 (congrArg Subtype.val h)
  lt x := (G.lt x.1).bind fun p ↦ if hp : p.1 = e then none else some (⟨p.1, hp⟩, p.2)
  lt_ι x := by
    simp only [Perm.subtypePerm_apply, G.lt_ι]
    cases h : G.lt x.1 with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.bind_some]
      split_ifs <;> rfl
  lt_unique l := by
    obtain ⟨x, hx, hu⟩ := G.lt_unique l.1
    have hxa : x ≠ a := fun h ↦ l.2 (by
      rw [h, ha] at hx; simp only [Option.some.injEq, Prod.mk.injEq, and_true] at hx
      exact hx.symm)
    have hxb : x ≠ G.ι a := fun h ↦ by
      rw [h, G.lt_ι, ha] at hx; simp at hx
    refine ⟨⟨x, hxa, hxb⟩, by simp [hx, l.2], fun y hy ↦ Subtype.ext (hu _ ?_)⟩
    cases h : G.lt y.1 with
    | none => simp [h] at hy
    | some p =>
      simp only [h, Option.bind_some] at hy
      split_ifs at hy with hp
      obtain ⟨p1, p2⟩ := p
      simp only [Option.some.injEq, Prod.mk.injEq, Subtype.ext_iff] at hy
      rw [h, hy.1, hy.2]
  pot x z := G.pot x.1 z.1
  pot_σ x := by
    obtain ⟨k, hk⟩ := exists_pow_skip₂ G.σ a (G.ι a) x.1
    simp only [Perm.subtypePerm_apply, hk]
    clear hk
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Perm.mul_apply, G.pot_σ, ih]
  pot_ι x hx z := by
    have hx' : G.lt x.1 = none := by
      cases h : G.lt x.1 with
      | none => rfl
      | some p =>
        simp [h, Option.bind_some, dif_neg (G.lt_live ha x.2 h)] at hx
    simpa [Subtype.ext_iff] using G.pot_ι x.1 hx' z.1
  dep x := G.dep x.1
  dep_σ x := by
    obtain ⟨k, hk⟩ := exists_pow_skip₂ G.σ a (G.ι a) x.1
    simp only [Perm.subtypePerm_apply, hk]
    clear hk
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Perm.mul_apply, G.dep_σ, ih]
  root x y hx hy := by
    rw [sameCycle_subtypePerm_iff, sameCycle_skip_iff x.2.2 y.2.2,
      sameCycle_skip_iff x.2.1 y.2.1]
    exact G.root x.1 y.1 hx hy
  parent x hx := by
    obtain ⟨p, hp, hxp, hd⟩ := G.parent x.1 hx
    have hpa : p ≠ a := fun h ↦ by rw [h, ha] at hp; simp at hp
    have hpb : p ≠ G.ι a := fun h ↦ by rw [h, G.lt_ι, ha] at hp; simp at hp
    refine ⟨⟨p, hpa, hpb⟩, by simp [hp], ?_, hd⟩
    rw [sameCycle_subtypePerm_iff, sameCycle_skip_iff x.2.2 hpb, sameCycle_skip_iff x.2.1 hpa]
    exact hxp

/-! ### Faces after deleting a non-tree edge -/

lemma delete_φ_apply (x : G.Live a) :
    ((G.delete ha).φ x).1 = skip (skip (G.φ * swap a (G.ι a)) a) (G.ι a) x.1 := by
  have hy1 : G.ι x.1 ≠ a := ((G.ι_live a x.1).2 x.2).1
  have hy2 : G.ι x.1 ≠ G.ι a := ((G.ι_live a x.1).2 x.2).2
  have hab := G.ne_ι a
  change skip (skip G.σ a) (G.ι a) (G.ι x.1) = _
  rw [skip_apply_eq_ite (π := skip G.σ a) hy2, skip_apply_eq_ite (π := G.σ) hy1,
    skip_apply_eq_ite (π := G.σ) (x := G.ι a) hab.symm,
    skip_apply_eq_ite (π := skip (G.φ * swap a (G.ι a)) a) x.2.2,
    skip_apply_eq_ite (π := G.φ * swap a (G.ι a)) x.2.1,
    skip_apply_eq_ite (π := G.φ * swap a (G.ι a)) (x := G.ι a) hab.symm,
    mul_swap_apply_of_ne G.φ x.2.1 x.2.2, mul_swap_apply_left, mul_swap_apply_right, φ_apply,
    φ_apply, φ_apply, G.ι_ι]

lemma delete_φ_eq : (G.delete ha).φ =
    (skip (skip (G.φ * swap a (G.ι a)) a) (G.ι a)).subtypePerm (skip₂_live _ (G.ne_ι a)) :=
  Equiv.ext fun x ↦ Subtype.ext (G.delete_φ_apply ha x)

lemma delete_sameCycle (x y : G.Live a) :
    (G.delete ha).φ.SameCycle x y ↔ (G.φ * swap a (G.ι a)).SameCycle x.1 y.1 := by
  rw [delete_φ_eq, sameCycle_subtypePerm_iff, sameCycle_skip_iff x.2.2 y.2.2,
    sameCycle_skip_iff x.2.1 y.2.1]

omit ha

variable (e) in
/-- `F(L) ≃ F(Option {l ≠ e})`, `e ↦ none`. -/
abbrev κ : FreeGroup L ≃* FreeGroup (Option {l : L // l ≠ e}) :=
  freeGroupCongr (optionSubtypeNe e).symm

variable (e) in
/-- The inclusion `F(L ∖ e) → F(Option (L ∖ e))`. -/
abbrev ι' : FreeGroup {l : L // l ≠ e} →* FreeGroup (Option {l : L // l ≠ e}) := FreeGroup.map some

variable (e) in
/-- The retraction `F(Option (L ∖ e)) → F(L ∖ e)` killing `none`. -/
def ρ' : FreeGroup (Option {l : L // l ≠ e}) →* FreeGroup {l : L // l ≠ e} :=
  FreeGroup.lift fun o ↦ o.elim 1 of

omit [DecidableEq L] in
lemma ρ'_ι' (x : FreeGroup {l : L // l ≠ e}) : ρ' e (ι' e x) = x := by
  have : (ρ' e).comp (ι' e) = MonoidHom.id _ := FreeGroup.ext_hom _ _ fun l ↦ by simp [ρ']
  exact DFunLike.congr_fun this x

omit [DecidableEq L] in
lemma isConj_of_ι' {x y : FreeGroup {l : L // l ≠ e}} (h : IsConj (ι' e x) (ι' e y)) :
    IsConj x y := by
  simpa [ρ'_ι'] using isConj_map (ρ' e) h

variable (a e) in
/-- The labels with the deleted edge erased, in `F(Option (L ∖ e))`. -/
def lab₀ (y : D) : FreeGroup (Option {l : L // l ≠ e}) :=
  if y = a ∨ y = G.ι a then 1 else κ e (G.lab y)

omit [Finite D] in
lemma lab₀_a : G.lab₀ a e a = 1 := by simp [lab₀]

omit [Finite D] in
lemma lab₀_b : G.lab₀ a e (G.ι a) = 1 := by simp [lab₀]

omit [Finite D] in
lemma lab₀_eq {y : D} (h1 : y ≠ a) (h2 : y ≠ G.ι a) : G.lab₀ a e y = κ e (G.lab y) := by
  simp [lab₀, h1, h2]

include ha

omit [Finite D] in
lemma κ_lab_a : κ e (G.lab a) = of none := by
  simp [lab, ha, labOf]

omit [Finite D] in
lemma κ_lab_b : κ e (G.lab (G.ι a)) = (of none)⁻¹ := by
  rw [lab_ι, _root_.map_inv, G.κ_lab_a ha]

lemma delete_lab (x : G.Live a) : ι' e ((G.delete ha).lab x) = κ e (G.lab x.1) := by
  cases h : G.lt x.1 with
  | none => simp [lab, delete, h, labOf]
  | some p =>
    obtain ⟨l, c⟩ := p
    have hl : l ≠ e := G.lt_live ha x.2 h
    cases c <;> simp [lab, delete, h, labOf, hl, optionSubtypeNe_symm_of_ne hl]

lemma lab₀_live (x : G.Live a) : G.lab₀ a e x.1 = ι' e ((G.delete ha).lab x) := by
  rw [G.lab₀_eq x.2.1 x.2.2, G.delete_lab ha]

lemma lab₀_fixed (y : D) : ι' e (ρ' e (G.lab₀ a e y)) = G.lab₀ a e y := by
  by_cases h : y = a ∨ y = G.ι a
  · simp [lab₀, h]
  · simp only [not_or] at h
    rw [G.lab₀_live ha ⟨y, h⟩, ρ'_ι']

lemma pathWord_lab₀_fixed (π : Perm D) (x : D) (n : ℕ) :
    ι' e (ρ' e (pathWord π (G.lab₀ a e) x n)) = pathWord π (G.lab₀ a e) x n :=
  (pathWord_congr ((ι' e).comp (ρ' e)) fun _ _ ↦ (G.lab₀_fixed ha _).symm).symm

lemma faceWord_lab₀_fixed (π : Perm D) (x : D) :
    ι' e (ρ' e (faceWord π (G.lab₀ a e) x)) = faceWord π (G.lab₀ a e) x :=
  G.pathWord_lab₀_fixed ha π x _

lemma delete_faceWord (x : G.Live a) :
    ι' e (faceWord (G.delete ha).φ (G.delete ha).lab x) =
      faceWord (G.φ * swap a (G.ι a)) (G.lab₀ a e) x.1 := by
  rw [← map_faceWord, show (ι' e ∘ (G.delete ha).lab) = G.lab₀ a e ∘ Subtype.val from
    funext fun x ↦ (G.lab₀_live ha x).symm, delete_φ_eq, faceWord_subtypePerm,
    faceWord_skip G.lab₀_b x.2.2, faceWord_skip G.lab₀_a x.2.1]

lemma isEmpty_letters (h : IsEmpty (G.Live a)) : IsEmpty {l : L // l ≠ e} :=
  ⟨fun l ↦ isEmptyElim ((G.delete ha).lt_unique l).choose⟩

omit ha in
lemma card_letters [Finite L] : Nat.card {l : L // l ≠ e} + 1 = Nat.card L := by
  have := Fintype.ofFinite L
  rw [← Nat.card_congr (optionSubtypeNe e), Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_option]

end Delete

/-! ### The induction step -/

section Step

variable [Finite D] [DecidableEq L] [Finite L] {a : D} {e : L} (ha : G.lt a = some (e, true))

omit [Finite L] in
lemma isConj_κ_symm {g R : ℕ} (Ψ : SurfaceGroup g R ≃* FreeGroup (Option {l : L // l ≠ e}))
    (j : Fin R) (x : D) (h : IsConj (Ψ (cusp j)) (faceWord G.φ (κ e ∘ G.lab) x)) :
    IsConj ((Ψ.trans (κ e).symm) (cusp j)) (faceWord G.φ G.lab x) := by
  have heq : (κ e).symm (faceWord G.φ (κ e ∘ G.lab) x) = faceWord G.φ G.lab x := by
    rw [map_faceWord, MulEquiv.symm_apply_apply]
  have := isConj_map (κ e).symm h
  rwa [heq] at this

include ha

/-- **Merge step**: if the deleted edge separates two distinct faces. -/
theorem isGeom_merge (hab : ¬ G.φ.SameCycle a (G.ι a)) (h'' : (G.delete ha).IsGeom) :
    G.IsGeom := by
  classical
  obtain ⟨g, R'', Ψ'', ν'', hcard, hν, hsurj, hconj⟩ := h''
  have hab' : a ≠ G.ι a := G.ne_ι a
  obtain ⟨horb, hword, hwa, hwb⟩ := merge G.φ (lab := κ e ∘ G.lab) (lab₀ := G.lab₀ a e) hab
    G.lab₀_a G.lab₀_b (fun y h1 h2 ↦ G.lab₀_eq h1 h2)
  set ψ := G.φ * swap a (G.ι a) with hψ
  set A := pathWord G.φ (G.lab₀ a e) (G.φ a) (per G.φ a - 1) with hA
  set B := pathWord G.φ (G.lab₀ a e) (G.φ (G.ι a)) (per G.φ (G.ι a) - 1) with hB
  -- the merged face of the smaller graph
  have hj₀ : ∃ j₀ : Fin R'', IsConj (Ψ'' (cusp j₀)) (ρ' e (A * B)) ∧
      ∀ x : G.Live a, ν'' x = j₀ ↔ ψ.SameCycle a x.1 := by
    by_cases hlive : ∃ x : G.Live a, ψ.SameCycle a x.1
    · obtain ⟨x₀, hx₀⟩ := hlive
      refine ⟨ν'' x₀, (hconj x₀).trans (isConj_of_ι' ?_), fun x ↦ ?_⟩
      · rw [G.delete_faceWord ha, ← hword, G.faceWord_lab₀_fixed ha]
        exact isConj_faceWord_of_sameCycle _ hx₀.symm
      · rw [hν, G.delete_sameCycle ha]
        exact ⟨fun h ↦ hx₀.trans h.symm, fun h ↦ h.symm.trans hx₀⟩
    · have hS : ∀ y, ψ.SameCycle a y → y = a ∨ y = G.ι a := fun y hy ↦ by
        by_contra hc
        simp only [not_or] at hc
        exact hlive ⟨⟨y, hc⟩, hy⟩
      have hall : ∀ y, y = a ∨ y = G.ι a := by
        refine G.connected (S := fun y ↦ y = a ∨ y = G.ι a) ?_ ?_ (Or.inl rfl)
        · rintro y (rfl | rfl)
          · rw [σ_eq_φ]
            exact hS _ ((horb _).2 (Or.inr (Perm.sameCycle_apply_right.2 (.refl _ _))))
          · rw [σ_eq_φ, G.ι_ι]
            exact hS _ ((horb _).2 (Or.inl (Perm.sameCycle_apply_right.2 (.refl _ _))))
        · rintro y (rfl | rfl)
          · exact Or.inr rfl
          · exact Or.inl (G.ι_ι a)
      have hD : IsEmpty (G.Live a) := ⟨fun x ↦ (hall x.1).elim x.2.1 x.2.2⟩
      have hL := G.isEmpty_letters ha hD
      have hR : R'' = 1 := by
        have : Nat.card {l : L // l ≠ e} = 0 := Nat.card_of_isEmpty
        omega
      subst hR
      exact ⟨0, isConj_iff.2 ⟨1, Subsingleton.elim _ _⟩, fun x ↦ isEmptyElim x⟩
  obtain ⟨j₀, hj₀c, hj₀ν⟩ := hj₀
  obtain ⟨R, rfl⟩ : ∃ R, R'' = R + 1 := ⟨R'' - 1, by have := j₀.2; omega⟩
  obtain ⟨Ψ₁, π, hπ, -, -, hc₁⟩ := exists_cusp_last Ψ'' j₀
  have hc₁' : IsConj (Ψ₁ (cusp (Fin.last R))) (ρ' e (A * B)) :=
    (hc₁ _).trans (by rw [hπ]; exact hj₀c)
  obtain ⟨u, hu⟩ := isConj_iff.1 hc₁'
  have hpq : Ψ₁ (cusp (Fin.last R)) = (u⁻¹ * ρ' e A) * (ρ' e B * u) := by
    rw [show Ψ₁ (cusp (Fin.last R)) = u⁻¹ * (u * Ψ₁ (cusp (Fin.last R)) * u⁻¹) * u by group, hu,
      _root_.map_mul]
    group
  set Ψ₂ := splitCusp Ψ₁ (u⁻¹ * ρ' e A) (ρ' e B * u) u hpq
  have hιA : ι' e (ρ' e A) = A := G.pathWord_lab₀_fixed ha _ _ _
  have hιB : ι' e (ρ' e B) = B := G.pathWord_lab₀_fixed ha _ _ _
  have hlive : ∀ x, ¬ G.φ.SameCycle a x → ¬ G.φ.SameCycle (G.ι a) x → x ≠ a ∧ x ≠ G.ι a :=
    fun x h1 h2 ↦ ⟨fun h ↦ h1 (h ▸ .refl _ _), fun h ↦ h2 (h ▸ .refl _ _)⟩
  have hπne : ∀ x (h1 : ¬ G.φ.SameCycle a x) (h2 : ¬ G.φ.SameCycle (G.ι a) x),
      π.symm (ν'' ⟨x, hlive x h1 h2⟩) ≠ Fin.last R := by
    intro x h1 h2 h
    rw [Equiv.symm_apply_eq, hπ, hj₀ν, horb] at h
    exact h.elim h1 h2
  let ν : D → Fin (R + 2) := fun x ↦
    if h1 : G.φ.SameCycle a x then (Fin.last R).castSucc
    else if h2 : G.φ.SameCycle (G.ι a) x then Fin.last (R + 1)
    else (π.symm (ν'' ⟨x, hlive x h1 h2⟩)).castSucc
  have hνother : ∀ x (h1 : ¬ G.φ.SameCycle a x) (h2 : ¬ G.φ.SameCycle (G.ι a) x),
      ν x = (π.symm (ν'' ⟨x, hlive x h1 h2⟩)).castSucc ∧ (ν x : ℕ) < R := fun x h1 h2 ↦ by
    have hne := hπne x h1 h2
    have hlt := Fin.val_lt_last hne
    have e1 : ν x = (π.symm (ν'' ⟨x, hlive x h1 h2⟩)).castSucc := by
      simp only [ν, dif_neg h1, dif_neg h2]
    refine ⟨e1, ?_⟩
    rw [e1, Fin.val_castSucc]
    exact hlt
  have hνa : ∀ x, G.φ.SameCycle a x → ν x = (Fin.last R).castSucc := fun x h ↦ by
    simp [ν, h]
  have hνb : ∀ x, G.φ.SameCycle (G.ι a) x → ν x = Fin.last (R + 1) := fun x h ↦ by
    have h1 : ¬ G.φ.SameCycle a x := fun h' ↦ hab (h'.trans h.symm)
    simp [ν, h1, h]
  refine ⟨g, R + 2, Ψ₂.trans (κ e).symm, ν, ?_, fun x y ↦ ?_, fun _ j ↦ ?_, fun x ↦ ?_⟩
  · have := card_letters (e := e)
    omega
  · -- `ν` separates the faces
    by_cases hxa : G.φ.SameCycle a x
    · rw [hνa x hxa]
      by_cases hya : G.φ.SameCycle a y
      · rw [hνa y hya]; exact ⟨fun _ ↦ hxa.symm.trans hya, fun _ ↦ rfl⟩
      by_cases hyb : G.φ.SameCycle (G.ι a) y
      · rw [hνb y hyb]
        exact ⟨fun h ↦ absurd (congrArg Fin.val h) (by simp),
          fun h ↦ absurd (hxa.trans h) hya⟩
      · obtain ⟨-, hlt⟩ := hνother y hya hyb
        exact ⟨fun h ↦ absurd (congrArg Fin.val h) (by simp; omega),
          fun h ↦ absurd (hxa.trans h) hya⟩
    by_cases hxb : G.φ.SameCycle (G.ι a) x
    · rw [hνb x hxb]
      by_cases hyb : G.φ.SameCycle (G.ι a) y
      · rw [hνb y hyb]; exact ⟨fun _ ↦ hxb.symm.trans hyb, fun _ ↦ rfl⟩
      by_cases hya : G.φ.SameCycle a y
      · rw [hνa y hya]
        exact ⟨fun h ↦ absurd (congrArg Fin.val h) (by simp),
          fun h ↦ absurd (hxb.trans h) hyb⟩
      · obtain ⟨-, hlt⟩ := hνother y hya hyb
        exact ⟨fun h ↦ absurd (congrArg Fin.val h) (by simp; omega),
          fun h ↦ absurd (hxb.trans h) hyb⟩
    obtain ⟨hx, hxlt⟩ := hνother x hxa hxb
    by_cases hya : G.φ.SameCycle a y
    · rw [hνa y hya]
      exact ⟨fun h ↦ absurd (congrArg Fin.val h) (by simp; omega),
        fun h ↦ absurd (hya.trans h.symm) hxa⟩
    by_cases hyb : G.φ.SameCycle (G.ι a) y
    · rw [hνb y hyb]
      exact ⟨fun h ↦ absurd (congrArg Fin.val h) (by simp; omega),
        fun h ↦ absurd (hyb.trans h.symm) hxb⟩
    obtain ⟨hy, -⟩ := hνother y hya hyb
    rw [hx, hy, (Fin.castSucc_injective _).eq_iff, π.symm.injective.eq_iff, hν,
      G.delete_sameCycle ha]
    exact sameCycle_mul_swap_iff_of_not G.φ (fun h ↦ hxa h.symm) (fun h ↦ hxb h.symm) y
  · -- surjectivity
    induction j using Fin.lastCases with
    | last => exact ⟨G.ι a, hνb _ (.refl _ _)⟩
    | cast j =>
      induction j using Fin.lastCases with
      | last => exact ⟨a, hνa _ (.refl _ _)⟩
      | cast k =>
        have hne : Nonempty (G.Live a) := by
          by_contra hc
          rw [not_nonempty_iff] at hc
          have hL := G.isEmpty_letters ha hc
          have : Nat.card {l : L // l ≠ e} = 0 := Nat.card_of_isEmpty
          have := k.2
          omega
        obtain ⟨x, hx⟩ := hsurj hne (π k.castSucc)
        have h1 : ¬ G.φ.SameCycle a x.1 := fun h ↦ by
          have := (hj₀ν x).2 ((horb _).2 (Or.inl h))
          rw [hx, ← hπ] at this
          exact absurd (π.injective this) (Fin.castSucc_lt_last k).ne
        have h2 : ¬ G.φ.SameCycle (G.ι a) x.1 := fun h ↦ by
          have := (hj₀ν x).2 ((horb _).2 (Or.inr h))
          rw [hx, ← hπ] at this
          exact absurd (π.injective this) (Fin.castSucc_lt_last k).ne
        refine ⟨x.1, ?_⟩
        rw [(hνother x.1 h1 h2).1]
        simp [hx]
  · -- conjugacy
    refine G.isConj_κ_symm Ψ₂ (ν x) x ?_
    by_cases hxa : G.φ.SameCycle a x
    · rw [hνa x hxa, splitCusp_cusp_castSucc_last]
      refine IsConj.trans ?_ (isConj_faceWord_of_sameCycle _ hxa)
      rw [hwa, Function.comp_apply, G.κ_lab_a ha, _root_.map_mul, _root_.map_inv, hιA]
      exact isConj_iff.2 ⟨ι' e u, by group⟩
    by_cases hxb : G.φ.SameCycle (G.ι a) x
    · rw [hνb x hxb, splitCusp_cusp_last]
      refine IsConj.trans ?_ (isConj_faceWord_of_sameCycle _ hxb)
      rw [hwb, Function.comp_apply, G.κ_lab_b ha, _root_.map_mul, hιB]
      exact isConj_iff.2 ⟨B * ι' e u, by group⟩
    · obtain ⟨hx, -⟩ := hνother x hxa hxb
      have hk := hπne x hxa hxb
      have hk' := Fin.castSucc_castPred _ hk
      rw [hx, ← hk', splitCusp_cusp, hk']
      have h0 := hconj ⟨x, hlive x hxa hxb⟩
      rw [← Equiv.apply_symm_apply π (ν'' ⟨x, hlive x hxa hxb⟩)] at h0
      have h1 := (hc₁ (π.symm (ν'' ⟨x, hlive x hxa hxb⟩))).trans h0
      have h2 := isConj_map (ι' e) h1
      rw [G.delete_faceWord ha, faceWord_mul_swap_of_not G.φ (fun y h1 h2 ↦ G.lab₀_eq h1 h2)
        (fun h ↦ hxa h.symm) (fun h ↦ hxb h.symm)] at h2
      exact h2

/-- **Split step**: if both sides of the deleted edge lie on the same face. -/
theorem isGeom_split (hab : G.φ.SameCycle a (G.ι a)) (h'' : (G.delete ha).IsGeom) :
    G.IsGeom := by
  classical
  obtain ⟨g, R'', Ψ'', ν'', hcard, hν, hsurj, hconj⟩ := h''
  have hab' : a ≠ G.ι a := G.ne_ι a
  obtain ⟨j, hj0, hjm, hnot, horbA, horbB, horb, hwA, hwB, hw⟩ :=
    split G.φ (lab := κ e ∘ G.lab) (lab₀ := G.lab₀ a e) hab hab' G.lab₀_a G.lab₀_b
      (fun y h1 h2 ↦ G.lab₀_eq h1 h2)
  set ψ := G.φ * swap a (G.ι a) with hψ
  set Y := pathWord G.φ (G.lab₀ a e) (G.φ (G.ι a)) (per G.φ a - j - 1) with hY
  set X := pathWord G.φ (G.lab₀ a e) (G.φ a) (j - 1) with hX
  -- the two arcs contain live darts (non-tree edges are not bridges)
  have hσa : G.σ a ≠ a := G.σ_ne_of_lt_ne_none (by rw [ha]; simp)
  have hσb : G.σ (G.ι a) ≠ G.ι a := G.σ_ne_of_lt_ne_none (by rw [G.lt_ι, ha]; simp)
  have hφb : G.φ (G.ι a) ≠ G.ι a := fun h ↦ hab' ((hab.symm.eq_of_left h).symm)
  have hφa : G.φ a ≠ a := fun h ↦ hab' (hab.eq_of_left h)
  have hla : G.φ (G.ι a) ≠ a ∧ G.φ (G.ι a) ≠ G.ι a := ⟨by rw [φ_apply, G.ι_ι]; exact hσa, hφb⟩
  have hlb : G.φ a ≠ a ∧ G.φ a ≠ G.ι a := ⟨hφa, by rw [φ_apply]; exact hσb⟩
  set xa : G.Live a := ⟨G.φ (G.ι a), hla⟩
  set xb : G.Live a := ⟨G.φ a, hlb⟩
  have hxa : ψ.SameCycle a xa.1 := by
    change ψ.SameCycle a (G.φ (G.ι a))
    rw [← mul_swap_apply_left G.φ (a := a) (b := G.ι a)]
    exact Perm.sameCycle_apply_right.2 (.refl _ _)
  have hxb : ψ.SameCycle (G.ι a) xb.1 := by
    change ψ.SameCycle (G.ι a) (G.φ a)
    rw [← mul_swap_apply_right G.φ (a := a) (b := G.ι a)]
    exact Perm.sameCycle_apply_right.2 (.refl _ _)
  have hAB : ν'' xb ≠ ν'' xa := fun h ↦ by
    rw [hν, G.delete_sameCycle ha] at h
    exact hnot (hxa.trans (h.symm.trans hxb.symm))
  have hcA : IsConj (Ψ'' (cusp (ν'' xa))) (ρ' e Y) := (hconj xa).trans (isConj_of_ι' (by
    rw [G.delete_faceWord ha, G.pathWord_lab₀_fixed ha, ← hY, ← hwA]
    exact isConj_faceWord_of_sameCycle _ hxa.symm))
  have hcB : IsConj (Ψ'' (cusp (ν'' xb))) (ρ' e X) := (hconj xb).trans (isConj_of_ι' (by
    rw [G.delete_faceWord ha, G.pathWord_lab₀_fixed ha, ← hX, ← hwB]
    exact isConj_faceWord_of_sameCycle _ hxb.symm))
  obtain ⟨R, rfl⟩ : ∃ R, R'' = R + 2 := ⟨R'' - 2, by
    have h1 := (ν'' xa).2
    have h2 := (ν'' xb).2
    have h3 : ((ν'' xb : ℕ)) ≠ ν'' xa := fun h ↦ hAB (Fin.ext h)
    omega⟩
  obtain ⟨Ψ₂, π, hπ₁, hπ₂, hc⟩ := exists_cusp_last₂ Ψ'' hAB
  have hcB' : IsConj (Ψ₂ (cusp (Fin.last R).castSucc)) (ρ' e X) :=
    (hc _).trans (by rw [hπ₂]; exact hcB)
  have hcA' : IsConj (Ψ₂ (cusp (Fin.last (R + 1)))) (ρ' e Y) :=
    (hc _).trans (by rw [hπ₁]; exact hcA)
  obtain ⟨u, hu⟩ := isConj_iff.1 hcB'
  obtain ⟨v, hv⟩ := isConj_iff.1 hcA'
  have hιX : ι' e (ρ' e X) = X := G.pathWord_lab₀_fixed ha _ _ _
  have hιY : ι' e (ρ' e Y) = Y := G.pathWord_lab₀_fixed ha _ _ _
  set Ψ₃ := addHandle Ψ₂ u⁻¹ v
  have hlive : ∀ x, ¬ G.φ.SameCycle a x → x ≠ a ∧ x ≠ G.ι a :=
    fun x h1 ↦ ⟨fun h ↦ h1 (h ▸ .refl _ _), fun h ↦ h1 (h ▸ hab)⟩
  have hτ : ∀ x (h1 : ¬ G.φ.SameCycle a x),
      π.symm (ν'' ⟨x, hlive x h1⟩) ≠ Fin.last (R + 1) ∧
        π.symm (ν'' ⟨x, hlive x h1⟩) ≠ (Fin.last R).castSucc := by
    intro x h1
    constructor
    · intro h
      rw [Equiv.symm_apply_eq, hπ₁, hν, G.delete_sameCycle ha] at h
      exact h1 (horbA _ (hxa.trans h.symm))
    · intro h
      rw [Equiv.symm_apply_eq, hπ₂, hν, G.delete_sameCycle ha] at h
      exact h1 (horbB _ (hxb.trans h.symm))
  let ν : D → Fin (R + 1) := fun x ↦
    if h1 : G.φ.SameCycle a x then Fin.last R
    else (π.symm (ν'' ⟨x, hlive x h1⟩)).castPred (hτ x h1).1
  have hνa : ∀ x, G.φ.SameCycle a x → ν x = Fin.last R := fun x h ↦ by simp [ν, h]
  have hνo : ∀ x (h1 : ¬ G.φ.SameCycle a x),
      (ν x).castSucc = π.symm (ν'' ⟨x, hlive x h1⟩) ∧ ν x ≠ Fin.last R := fun x h1 ↦ by
    have e1 : ν x = (π.symm (ν'' ⟨x, hlive x h1⟩)).castPred (hτ x h1).1 := by
      simp only [ν, dif_neg h1]
    refine ⟨by rw [e1, Fin.castSucc_castPred], fun h ↦ (hτ x h1).2 ?_⟩
    rw [← Fin.castSucc_castPred _ (hτ x h1).1, ← e1, h]
  refine ⟨g + 1, R + 1, Ψ₃.trans (κ e).symm, ν, ?_, fun x y ↦ ?_, fun _ k ↦ ?_, fun x ↦ ?_⟩
  · have := card_letters (e := e)
    omega
  · by_cases hxa' : G.φ.SameCycle a x
    · rw [hνa x hxa']
      by_cases hya : G.φ.SameCycle a y
      · rw [hνa y hya]; exact ⟨fun _ ↦ hxa'.symm.trans hya, fun _ ↦ rfl⟩
      · exact ⟨fun h ↦ absurd h.symm (hνo y hya).2, fun h ↦ absurd (hxa'.trans h) hya⟩
    by_cases hya : G.φ.SameCycle a y
    · rw [hνa y hya]
      exact ⟨fun h ↦ absurd h (hνo x hxa').2, fun h ↦ absurd (hya.trans h.symm) hxa'⟩
    rw [← (Fin.castSucc_injective _).eq_iff, (hνo x hxa').1, (hνo y hya).1,
      π.symm.injective.eq_iff, hν, G.delete_sameCycle ha]
    exact sameCycle_mul_swap_iff_of_not G.φ (fun h ↦ hxa' h.symm)
      (fun h ↦ hxa' (hab.trans h.symm)) y
  · by_cases hk : k = Fin.last R
    · exact ⟨a, by rw [hνa a (.refl _ _), hk]⟩
    obtain ⟨x, hx⟩ := hsurj ⟨xa⟩ (π k.castSucc)
    have h1 : ¬ G.φ.SameCycle a x.1 := fun h ↦ by
      rcases horb _ h with h' | h'
      · have : ν'' x = ν'' xa := by
          rw [hν, G.delete_sameCycle ha]; exact h'.symm.trans hxa
        rw [hx, ← hπ₁] at this
        exact absurd (π.injective this) (Fin.castSucc_lt_last k).ne
      · have : ν'' x = ν'' xb := by
          rw [hν, G.delete_sameCycle ha]; exact h'.symm.trans hxb
        rw [hx, ← hπ₂] at this
        exact hk (Fin.castSucc_injective _ (π.injective this))
    refine ⟨x.1, Fin.castSucc_injective _ ?_⟩
    rw [(hνo x.1 h1).1]
    simp [hx]
  · refine G.isConj_κ_symm Ψ₃ (ν x) x ?_
    by_cases hxa' : G.φ.SameCycle a x
    · rw [hνa x hxa']
      refine (isConj_addHandle_cusp_last Ψ₂ u⁻¹ v).trans
        (IsConj.trans ?_ (isConj_faceWord_of_sameCycle _ hxa'))
      rw [hw, Function.comp_apply, Function.comp_apply, G.κ_lab_a ha, G.κ_lab_b ha]
      have hC₁ : hC₁ Ψ₂ = (ι' e u)⁻¹ * X * ι' e u := by
        rw [hC₁, show Ψ₂ (cusp (Fin.last R).castSucc) =
          u⁻¹ * (u * Ψ₂ (cusp (Fin.last R).castSucc) * u⁻¹) * u by group, hu]
        simp [hιX]
      have hC₂ : hC₂ Ψ₂ = (ι' e v)⁻¹ * Y * ι' e v := by
        rw [hC₂, show Ψ₂ (cusp (Fin.last (R + 1))) =
          v⁻¹ * (v * Ψ₂ (cusp (Fin.last (R + 1))) * v⁻¹) * v by group, hv]
        simp [hιY]
      rw [hC₁, hC₂, hE]
      refine isConj_iff.2 ⟨(X * of none)⁻¹ * ι' e u, ?_⟩
      simp only [_root_.map_inv]
      group
    · obtain ⟨hx, hne⟩ := hνo x hxa'
      have hk' := Fin.castSucc_castPred _ hne
      rw [← hk', addHandle_cusp, Fin.castSucc_castPred _ hne, hx]
      have h0 := hconj ⟨x, hlive x hxa'⟩
      rw [← Equiv.apply_symm_apply π (ν'' ⟨x, hlive x hxa'⟩)] at h0
      have h2 := isConj_map (ι' e) ((hc (π.symm (ν'' ⟨x, hlive x hxa'⟩))).trans h0)
      rw [G.delete_faceWord ha, faceWord_mul_swap_of_not G.φ (fun y h1 h2 ↦ G.lab₀_eq h1 h2)
        (fun h ↦ hxa' h.symm) (fun h ↦ hxa' (hab.trans h.symm))] at h2
      exact h2

end Step

universe u v

theorem isGeom_aux (n : ℕ) : ∀ {D : Type u} {L : Type v} [DecidableEq D] [Finite D]
    [DecidableEq L] [Finite L] (G : RibbonData D L), Nat.card L = n → G.IsGeom := by
  induction n with
  | zero =>
    intro D L _ _ _ _ G hn
    have : IsEmpty L := Finite.card_eq_zero_iff.1 hn
    exact G.isGeom_of_isEmpty
  | succ n ih =>
    intro D L _ _ _ _ G hn
    have : Nonempty L := Nat.card_pos_iff.1 (by omega) |>.1
    obtain ⟨e⟩ := this
    obtain ⟨a, ha, -⟩ := G.lt_unique e
    have h'' := ih (G.delete ha) (by have := card_letters (e := e); omega)
    by_cases hab : G.φ.SameCycle a (G.ι a)
    · exact G.isGeom_split ha hab h''
    · exact G.isGeom_merge ha hab h''

/-- **Geometric bases of ribbon graphs.** The free group `F(L)` on the non-tree edges of a
ribbon graph is isomorphic to `Π_{g,R}`, `R` the number of faces, with each cusp going to a
conjugate of the face word of the corresponding face, and `|L| + 1 = 2g + R`. -/
theorem isGeom {D : Type u} {L : Type v} [DecidableEq D] [Finite D] [Finite L]
    (G : RibbonData D L) : G.IsGeom := by
  classical
  exact isGeom_aux _ G rfl

end RibbonData

end Pi1.Ribbon
