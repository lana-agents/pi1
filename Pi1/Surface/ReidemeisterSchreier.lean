/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.End

/-!
# The Reidemeister–Schreier theorem for subgroups of free groups

Let the free group `F(α)` act on a set `Ω` and fix `ω₀ : Ω`. A *Schreier transversal* is a
family of words `t ω` with `t ω • ω₀ = ω`, `t ω₀ = 1`, together with a set `E ⊆ Ω × α` of
*tree edges*: an edge `(ω, a)` (from `ω` to `a • ω`) lies in `E` only if its *Schreier generator*

  `s(ω, a) = t (a • ω)⁻¹ * a * t ω`

is trivial, and every `ω ≠ ω₀` is reached from a vertex of smaller depth by an edge of `E`
(in either direction). Then the stabiliser of `ω₀` is free on the Schreier generators of the
edges outside `E`:

  `Pi1.ReidemeisterSchreier.Transversal.basis T : FreeGroupBasis {e // e ∉ T.E} (stabilizer _ ω₀)`,
  `T.basis e = s(e)`.

This is the Reidemeister–Schreier theorem for free groups (Schreier's form of Nielsen–Schreier),
see Magnus–Karrass–Solitar, *Combinatorial Group Theory*, §2.3 (Theorems 2.7–2.9), or
Lyndon–Schupp, *Combinatorial Group Theory*, Ch. II, Prop. 4.1 and the Reidemeister–Schreier
method, §II.4. Mathlib's `subgroupIsFreeOfIsFree` proves freeness with an unspecified basis; here
the basis is explicit, which is what the computation of fundamental groups of finite coverings of
`ℂ ∖ {0, 1}` needs (the cusp loops are words in the Schreier generators).

## Proof

The inverse of `FreeGroup {e // e ∉ E} → stabilizer` is the *Reidemeister rewriting*: `F(α)`
acts on `Ω × F(E^c)` by `a • (ω, u) = (a • ω, ℓ(ω, a) * u)` with `ℓ(ω, a) = 1` on tree edges and
the generator `(ω, a)` otherwise (`extAction`). The second component of `h • (ω₀, 1)` is a
homomorphism on the stabiliser (`rewrite`), it sends `s(e)` to `ℓ(e)` because the words `t ω`
travel along tree edges only (`coc_t`), so it is a left inverse. Surjectivity is the telescoping
identity `t (g h ω)⁻¹ * (g * h) * t ω = (t (g (h ω))⁻¹ * g * t (h ω)) * (t (h ω)⁻¹ * h * t ω)`.
-/

@[expose] public section

namespace Pi1.ReidemeisterSchreier

open FreeGroup

variable {α Ω G : Type*} [MulAction (FreeGroup α) Ω] [Group G]

/-! ### The extended action on `Ω × G` -/

/-- The permutation of `Ω × G` attached to a letter `a` and a labelling `lab` of the edges:
`(ω, u) ↦ (a • ω, lab ω a * u)`. -/
def genPerm (lab : Ω → α → G) (a : α) : Equiv.Perm (Ω × G) where
  toFun p := (of a • p.1, lab p.1 a * p.2)
  invFun p := ((of a)⁻¹ • p.1, (lab ((of a)⁻¹ • p.1) a)⁻¹ * p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- The action of `F(α)` on `Ω × G` determined by the labelling `lab`. -/
def extAction (lab : Ω → α → G) : FreeGroup α →* Equiv.Perm (Ω × G) :=
  FreeGroup.lift (genPerm lab)

lemma extAction_of (lab : Ω → α → G) (a : α) : extAction lab (of a) = genPerm lab a :=
  FreeGroup.lift_apply_of

lemma extAction_fst (lab : Ω → α → G) (g : FreeGroup α) (p : Ω × G) :
    (extAction lab g p).1 = g • p.1 := by
  induction g using FreeGroup.induction_on generalizing p with
  | C1 => simp
  | of a => simp [extAction_of, genPerm]
  | inv_of x ih =>
    rw [_root_.map_inv]
    have h := ih ((extAction lab (of x))⁻¹ p)
    rw [show extAction lab (of x) ((extAction lab (of x))⁻¹ p) = p from
      Equiv.apply_symm_apply _ _] at h
    rw [h, inv_smul_smul]
  | mul x y hx hy => rw [_root_.map_mul, Equiv.Perm.mul_apply, hx, hy, mul_smul]

lemma extAction_mul_right (lab : Ω → α → G) (g : FreeGroup α) (p : Ω × G) (v : G) :
    extAction lab g (p.1, p.2 * v) = ((extAction lab g p).1, (extAction lab g p).2 * v) := by
  induction g using FreeGroup.induction_on generalizing p with
  | C1 => simp
  | of a => simp [extAction_of, genPerm, mul_assoc]
  | inv_of x ih =>
    rw [_root_.map_inv]
    set q := (extAction lab (of x))⁻¹ p
    have h := ih q
    have hq : extAction lab (of x) q = p := Equiv.apply_symm_apply _ _
    rw [hq] at h
    rw [← h]; exact Equiv.symm_apply_apply _ _
  | mul x y hx hy => rw [_root_.map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hy, hx]

/-- The cocycle of the extended action: `g • (ω, 1) = (g • ω, coc lab g ω)`. -/
def coc (lab : Ω → α → G) (g : FreeGroup α) (ω : Ω) : G := (extAction lab g (ω, 1)).2

lemma extAction_apply (lab : Ω → α → G) (g : FreeGroup α) (ω : Ω) (u : G) :
    extAction lab g (ω, u) = (g • ω, coc lab g ω * u) := by
  have h := extAction_mul_right lab g (ω, 1) u
  simp only [one_mul] at h
  rw [h, extAction_fst, coc]

lemma coc_mul (lab : Ω → α → G) (g h : FreeGroup α) (ω : Ω) :
    coc lab (g * h) ω = coc lab g (h • ω) * coc lab h ω := by
  have := extAction_apply lab (g * h) ω 1
  rw [_root_.map_mul, Equiv.Perm.mul_apply, extAction_apply, extAction_apply] at this
  simpa using (congrArg Prod.snd this).symm

@[simp] lemma coc_one (lab : Ω → α → G) (ω : Ω) : coc lab 1 ω = 1 := by
  simp [coc]

@[simp] lemma coc_of (lab : Ω → α → G) (a : α) (ω : Ω) : coc lab (of a) ω = lab ω a := by
  simp [coc, extAction_of, genPerm]

lemma coc_inv (lab : Ω → α → G) (g : FreeGroup α) (ω : Ω) :
    coc lab g⁻¹ (g • ω) = (coc lab g ω)⁻¹ := by
  have h := coc_mul lab g⁻¹ g ω
  rw [inv_mul_cancel, coc_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- The cocycle restricted to the stabiliser of `ω₀` is a homomorphism. -/
noncomputable def cocHom (lab : Ω → α → G) (ω₀ : Ω) :
    MulAction.stabilizer (FreeGroup α) ω₀ →* G where
  toFun h := coc lab h ω₀
  map_one' := coc_one _ _
  map_mul' g h := by
    simp only [Subgroup.coe_mul]
    rw [coc_mul, MulAction.mem_stabilizer_iff.mp h.2]

@[simp] lemma cocHom_apply (lab : Ω → α → G) (ω₀ : Ω) (h : MulAction.stabilizer (FreeGroup α) ω₀) :
    cocHom lab ω₀ h = coc lab h ω₀ := rfl

/-- A cocycle that is trivial on the generators is trivial. -/
lemma coc_eq_one (lab : Ω → α → G) (hlab : ∀ ω a, lab ω a = 1) (g : FreeGroup α) (ω : Ω) :
    coc lab g ω = 1 := by
  induction g using FreeGroup.induction_on generalizing ω with
  | C1 => simp
  | of a => simp [hlab]
  | inv_of a ih =>
    have h := coc_inv lab (of a) ((of a)⁻¹ • ω)
    rw [smul_inv_smul, ih, inv_one] at h
    exact h
  | mul x y hx hy => rw [coc_mul, hx, hy, one_mul]

/-- The cocycle along `bⁿ` only depends on the labels of the edges `(bⁱ • ω, b)`, `i < n`. -/
lemma coc_pow_congr {lab lab' : Ω → α → G} (b : α) (n : ℕ) (ω : Ω)
    (h : ∀ i < n, lab ((of b) ^ i • ω) b = lab' ((of b) ^ i • ω) b) :
    coc lab ((of b) ^ n) ω = coc lab' ((of b) ^ n) ω := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih =>
    have h0 := h 0 (by omega)
    rw [pow_zero, one_smul] at h0
    rw [pow_succ, coc_mul, coc_mul, coc_of, coc_of, h0, ih]
    intro i hi
    have := h (i + 1) (by omega)
    rwa [pow_succ, mul_smul] at this

/-- If `g` fixes `ω` with trivial cocycle, so do its powers. -/
lemma coc_zpow_eq_one {lab : Ω → α → G} {g : FreeGroup α} {ω : Ω} (hg : g • ω = ω)
    (hc : coc lab g ω = 1) (k : ℤ) : coc lab (g ^ k) ω = 1 := by
  let S : Subgroup (FreeGroup α) :=
    { carrier := {h | h • ω = ω ∧ coc lab h ω = 1}
      mul_mem' := fun {x y} hx hy ↦ ⟨by rw [mul_smul, hy.1, hx.1], by
        rw [coc_mul, hy.1, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨one_smul _ _, coc_one _ _⟩
      inv_mem' := fun {x} hx ↦ ⟨by rw [inv_smul_eq_iff, hx.1], by
        have := coc_inv lab x ω
        rwa [hx.1, hx.2, inv_one] at this⟩ }
  exact (zpow_mem (show g ∈ S from ⟨hg, hc⟩) k).2

/-! ### Schreier generators and transversals -/

/-- The Schreier generator `t (a • ω)⁻¹ * a * t ω` of the edge `(ω, a)`. -/
def schreierGen (t : Ω → FreeGroup α) (ω : Ω) (a : α) : FreeGroup α :=
  (t (of a • ω))⁻¹ * of a * t ω

/-- The telescoping identity behind the Reidemeister–Schreier rewriting. -/
lemma telescope (t : Ω → FreeGroup α) (g h : FreeGroup α) (ω : Ω) :
    (t ((g * h) • ω))⁻¹ * (g * h) * t ω =
      ((t (g • h • ω))⁻¹ * g * t (h • ω)) * ((t (h • ω))⁻¹ * h * t ω) := by
  simp only [mul_smul, mul_assoc, mul_inv_cancel_left]

variable (α) in
/-- A Schreier transversal for the action of `F(α)` on `Ω` based at `ω₀`, with its set `E` of
tree edges (see the module docstring). -/
structure Transversal (ω₀ : Ω) where
  /-- The coset representatives. -/
  t : Ω → FreeGroup α
  /-- The tree edges. -/
  E : Set (Ω × α)
  t_smul : ∀ ω, t ω • ω₀ = ω
  t_base : t ω₀ = 1
  schreierGen_eq_one : ∀ e ∈ E, schreierGen t e.1 e.2 = 1
  /-- A depth function witnessing that the tree edges connect every vertex to `ω₀`. -/
  depth : Ω → ℕ
  exists_edge : ∀ ω, ω ≠ ω₀ → ∃ e ∈ E,
    (e.1 = ω ∧ depth (of e.2 • ω) < depth ω) ∨ (of e.2 • e.1 = ω ∧ depth e.1 < depth ω)

namespace Transversal

variable {ω₀ : Ω} (T : Transversal α ω₀)

lemma schreierGen_mem (ω : Ω) (a : α) :
    schreierGen T.t ω a ∈ MulAction.stabilizer (FreeGroup α) ω₀ := by
  rw [MulAction.mem_stabilizer_iff, schreierGen, mul_smul, mul_smul, T.t_smul, inv_smul_eq_iff,
    T.t_smul]

/-- The set of edges outside the tree, indexing the Schreier basis. -/
abbrev Gens := {e : Ω × α // e ∉ T.E}

open scoped Classical in
/-- The labelling of edges used for the rewriting: `1` on tree edges, the generator otherwise. -/
noncomputable def lab (ω : Ω) (a : α) : FreeGroup T.Gens :=
  if h : (ω, a) ∈ T.E then 1 else of ⟨(ω, a), h⟩

lemma lab_of_mem {ω : Ω} {a : α} (h : (ω, a) ∈ T.E) : T.lab ω a = 1 := by
  simp [lab, h]

lemma lab_of_notMem (e : T.Gens) : T.lab e.1.1 e.1.2 = of e := by
  simp [lab, e.2]

lemma t_mul_eq {e : Ω × α} (he : e ∈ T.E) : T.t (of e.2 • e.1) = of e.2 * T.t e.1 := by
  have h := T.schreierGen_eq_one e he
  rwa [schreierGen, mul_assoc, inv_mul_eq_one] at h

/-- The coset representatives run along tree edges only: the cocycle of any labelling that is
trivial on tree edges vanishes on them. -/
lemma coc_t_of {G : Type*} [Group G] (lab : Ω → α → G) (hlab : ∀ e ∈ T.E, lab e.1 e.2 = 1)
    (ω : Ω) : coc lab (T.t ω) ω₀ = 1 := by
  induction hd : T.depth ω using Nat.strong_induction_on generalizing ω with
  | _ n ih =>
    by_cases hω : ω = ω₀
    · subst hω; simp [T.t_base]
    obtain ⟨⟨ω', a⟩, he, h | h⟩ := T.exists_edge ω hω
    · obtain ⟨rfl, hlt⟩ := h
      have ht : T.t ω' = (of a)⁻¹ * T.t (of a • ω') := by
        rw [T.t_mul_eq he, inv_mul_cancel_left]
      rw [ht, coc_mul, T.t_smul, ih _ (hd ▸ hlt) _ rfl, mul_one, coc_inv, coc_of,
        hlab _ he, inv_one]
    · obtain ⟨rfl, hlt⟩ := h
      rw [T.t_mul_eq he, coc_mul, T.t_smul, ih _ (hd ▸ hlt) _ rfl, mul_one, coc_of,
        hlab _ he]

lemma coc_t (ω : Ω) : coc T.lab (T.t ω) ω₀ = 1 :=
  T.coc_t_of T.lab (fun _ he ↦ T.lab_of_mem he) ω

lemma coc_schreierGen_of {G : Type*} [Group G] (lab : Ω → α → G)
    (hlab : ∀ e ∈ T.E, lab e.1 e.2 = 1) (ω : Ω) (a : α) :
    coc lab (schreierGen T.t ω a) ω₀ = lab ω a := by
  have h1 := coc_inv lab (T.t (of a • ω)) ω₀
  rw [T.t_smul, T.coc_t_of lab hlab, inv_one] at h1
  rw [schreierGen, coc_mul, coc_mul, T.coc_t_of lab hlab, mul_one, T.t_smul, h1, one_mul,
    coc_of]

lemma coc_schreierGen (ω : Ω) (a : α) : coc T.lab (schreierGen T.t ω a) ω₀ = T.lab ω a :=
  T.coc_schreierGen_of T.lab (fun _ he ↦ T.lab_of_mem he) ω a

/-- The Schreier generators, as a map from the free group on the non-tree edges. -/
noncomputable def toStab : FreeGroup T.Gens →* MulAction.stabilizer (FreeGroup α) ω₀ :=
  FreeGroup.lift fun e ↦ ⟨schreierGen T.t e.1.1 e.1.2, T.schreierGen_mem _ _⟩

@[simp] lemma toStab_of (e : T.Gens) :
    (T.toStab (of e) : FreeGroup α) = schreierGen T.t e.1.1 e.1.2 := by
  simp [toStab]

/-- The Reidemeister rewriting of an element of the stabiliser. -/
noncomputable def rewrite : MulAction.stabilizer (FreeGroup α) ω₀ →* FreeGroup T.Gens :=
  cocHom T.lab ω₀

lemma rewrite_comp_toStab : T.rewrite.comp T.toStab = MonoidHom.id _ := by
  refine FreeGroup.ext_hom _ _ fun e ↦ ?_
  change coc T.lab (T.toStab (of e) : FreeGroup α) ω₀ = of e
  rw [toStab_of, coc_schreierGen, lab_of_notMem]

lemma toStab_injective : Function.Injective T.toStab :=
  Function.LeftInverse.injective (g := T.rewrite) fun x ↦
    DFunLike.congr_fun T.rewrite_comp_toStab x

lemma schreierGen_mem_range (ω : Ω) (a : α) :
    schreierGen T.t ω a ∈ (T.toStab.range.map (Subgroup.subtype _)) := by
  by_cases he : (ω, a) ∈ T.E
  · rw [T.schreierGen_eq_one _ he]; exact one_mem _
  · exact ⟨T.toStab (of ⟨(ω, a), he⟩), ⟨_, rfl⟩, T.toStab_of _⟩

lemma conj_mem_range (g : FreeGroup α) (ω : Ω) :
    (T.t (g • ω))⁻¹ * g * T.t ω ∈ (T.toStab.range.map (Subgroup.subtype _)) := by
  induction g using FreeGroup.induction_on generalizing ω with
  | C1 => simp
  | of a => exact T.schreierGen_mem_range ω a
  | inv_of a _ =>
    have h := inv_mem (T.schreierGen_mem_range ((of a)⁻¹ • ω) a)
    simpa [schreierGen, mul_assoc] using h
  | mul x y hx hy =>
    rw [telescope]
    exact mul_mem (hx _) (hy _)

lemma toStab_surjective : Function.Surjective T.toStab := by
  intro h
  have := T.conj_mem_range h ω₀
  rw [MulAction.mem_stabilizer_iff.mp h.2, T.t_base, inv_one, one_mul, mul_one] at this
  obtain ⟨x, ⟨y, rfl⟩, hx⟩ := this
  exact ⟨y, Subtype.ext hx⟩

lemma rewrite_injective : Function.Injective T.rewrite := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := T.toStab_surjective x
  obtain ⟨y, rfl⟩ := T.toStab_surjective y
  have h := DFunLike.congr_fun T.rewrite_comp_toStab
  have hx := h x
  have hy := h y
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply] at hx hy
  rw [← hx, ← hy, hxy]

/-- **Reidemeister–Schreier**: the stabiliser of `ω₀` is free on the Schreier generators of the
non-tree edges. -/
noncomputable def basis : FreeGroupBasis T.Gens (MulAction.stabilizer (FreeGroup α) ω₀) :=
  .ofRepr (MulEquiv.ofBijective T.toStab ⟨T.toStab_injective, T.toStab_surjective⟩).symm

@[simp] lemma basis_apply (e : T.Gens) :
    (T.basis e : FreeGroup α) = schreierGen T.t e.1.1 e.1.2 := by
  change ((MulEquiv.ofBijective T.toStab _).symm.symm (of e) : FreeGroup α) = _
  rw [MulEquiv.symm_symm, MulEquiv.ofBijective_apply, toStab_of]

end Transversal

end Pi1.ReidemeisterSchreier
