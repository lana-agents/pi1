/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.SchreierTransversal
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Group

/-!
# Filling cusps in a finite-index subgroup of a free group

Let `F(α)` act on a finite set `Ω`, transitively, and let `A ⊆ α` be a finite set of letters. For
`a ∈ A` and `ω ∈ Ω` with `⟨a⟩`-orbit of length `m`, the element `t ω⁻¹ aᵐ t ω` of the stabiliser
`H` of `ω₀` is the *cusp loop* of the orbit; the *cusp subgroup* `cuspSubgroup A ω₀ ⊴ H` is the
normal closure of all elements of `H` of the form `g aᵏ g⁻¹` (`a ∈ A`, `g ∈ F(α)`, `k ∈ ℤ`), which
is the normal closure of the cusp loops.

**Theorem** (`nonempty_quotient_cuspSubgroup_mulEquiv`). `H ⧸ cuspSubgroup A ω₀` is free of rank
`|Ω| (|α| - 1) + 1 - ∑_{a ∈ A} #(⟨a⟩-orbits on Ω)`.

Topologically: for a finite covering `Y → ℂ ∖ {0, 1}` with monodromy `Ω` (`α = {x₀, x₁}`, the
loops around `0` and `1`), `H = π₁(Y)`, the `⟨xᵢ⟩`-orbits are the punctures of `Y` over `i`, and
the quotient is `π₁` of `Y` with the punctures over `0` and `1` filled in; this is how the
fundamental group of an affine curve `X ∖ f⁻¹(∞)` is computed from a Belyi map `f`.

## Proof

Take any Schreier transversal `T` (`Pi1.ReidemeisterSchreier.Parent.bfs`). In every
`⟨a⟩`-orbit (`a ∈ A`) some edge `(c, a)` is not a tree edge, since otherwise the cusp loop would
be trivial in the free group `H` (its Reidemeister rewriting vanishes, `exists_notMem_E`); choose
one such *chosen edge* per orbit (`chosen`). The cusp loop of the orbit of `c` is
`W · s(c, a)` where `W` only involves the other edges of the orbit; eliminating `s(c, a)` against
the relation `W · s(c, a) = 1` is a Tietze move. Concretely, the rewriting with labels
`ℓ'(c, a) = ℓ(W)⁻¹` on chosen edges and the Schreier labels elsewhere (`lab'`) is a surjection
`H → F(non-tree, non-chosen edges)` (`tau`) whose kernel is the cusp subgroup: it kills the cusp
loops (`coc_pow_per_chosen`), and conversely `ψ ∘ tau = mk` for the obvious
`ψ : F(non-tree, non-chosen edges) → H ⧸ cuspSubgroup` (`psi_tau`). The count follows from
Schreier's index formula (`Parent.card_gens`). This is the Reidemeister–Schreier method with
Tietze eliminations, cf. Magnus–Karrass–Solitar, *Combinatorial Group Theory*, §2.3 and §1.5.
-/

@[expose] public section

namespace Pi1.ReidemeisterSchreier

open FreeGroup

universe u v

variable {α : Type u} {Ω : Type v} [MulAction (FreeGroup α) Ω]

/-- The cusp subgroup of the stabiliser of `ω₀` for the letters in `A`: the normal closure of the
elements conjugate in `F(α)` to a power of a letter of `A`. -/
def cuspSubgroup (A : Set α) (ω₀ : Ω) : Subgroup (MulAction.stabilizer (FreeGroup α) ω₀) :=
  Subgroup.normalClosure
    {h | ∃ a ∈ A, ∃ g : FreeGroup α, ∃ k : ℤ, (h : FreeGroup α) = g * of a ^ k * g⁻¹}

instance (A : Set α) (ω₀ : Ω) : (cuspSubgroup A ω₀).Normal := Subgroup.normalClosure_normal

/-- The `⟨a⟩`-orbit of `ω`. -/
def orb (a : α) (ω : Ω) : MulAction.orbitRel.Quotient (Subgroup.zpowers (of a)) Ω :=
  Quotient.mk (MulAction.orbitRel (Subgroup.zpowers (of a)) Ω) ω

lemma orb_eq_iff {a : α} {ω ω' : Ω} : orb a ω = orb a ω' ↔ ∃ k : ℤ, (of a) ^ k • ω' = ω := by
  rw [orb, orb, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨_, Subgroup.zpow_mem_zpowers _ k⟩, rfl⟩

lemma orb_zpow_smul (a : α) (k : ℤ) (ω : Ω) : orb a ((of a) ^ k • ω) = orb a ω :=
  orb_eq_iff.mpr ⟨k, rfl⟩

lemma orb_surjective (a : α) : Function.Surjective (orb (Ω := Ω) a) :=
  Quotient.mk_surjective

/-- The length of the `⟨a⟩`-orbit of `ω`. -/
noncomputable abbrev per (a : α) (ω : Ω) : ℕ := Function.minimalPeriod (of a • ·) ω

lemma per_pos [Finite Ω] (a : α) (ω : Ω) : 0 < per a ω :=
  Function.minimalPeriod_pos_of_mem_periodicPts
    ((MulAction.injective (of a : FreeGroup α)).mem_periodicPts ω)

lemma pow_per_smul (a : α) (ω : Ω) : (of a) ^ per a ω • ω = ω :=
  MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mpr dvd_rfl

lemma of_pow_ne_one (a : α) {n : ℕ} (hn : 0 < n) : (of a) ^ n ≠ 1 := by
  intro h
  have h' := congrArg (FreeGroup.lift fun _ : α ↦ Multiplicative.ofAdd (1 : ℤ)) h
  simp only [map_pow, FreeGroup.lift_apply_of] at h'
  have h'' := congrArg Multiplicative.toAdd h'
  simp at h''
  omega

namespace Transversal

variable {ω₀ : Ω} (T : Transversal α ω₀)

/-- The element `t (g • ω)⁻¹ * g * t ω` of the stabiliser. -/
def cj (g : FreeGroup α) (ω : Ω) : MulAction.stabilizer (FreeGroup α) ω₀ :=
  ⟨(T.t (g • ω))⁻¹ * g * T.t ω, by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, T.t_smul, inv_smul_eq_iff, T.t_smul]⟩

@[simp] lemma cj_one (ω : Ω) : T.cj 1 ω = 1 := by
  ext; simp [cj]

lemma cj_mul (g h : FreeGroup α) (ω : Ω) : T.cj (g * h) ω = T.cj g (h • ω) * T.cj h ω := by
  ext; simp only [cj, Subgroup.coe_mul]; exact telescope T.t g h ω

lemma cj_inv (g : FreeGroup α) (ω : Ω) : T.cj g⁻¹ (g • ω) = (T.cj g ω)⁻¹ := by
  ext; simp only [cj, InvMemClass.coe_inv, inv_smul_smul]; group

lemma cj_of_stab (h : MulAction.stabilizer (FreeGroup α) ω₀) : T.cj h ω₀ = h := by
  ext; simp [cj, MulAction.mem_stabilizer_iff.mp h.2, T.t_base]

/-- In every `⟨a⟩`-orbit some edge with letter `a` is not a tree edge. -/
lemma exists_notMem_E [Finite Ω] (a : α) (ω : Ω) :
    ∃ i < per a ω, ((of a) ^ i • ω, a) ∉ T.E := by
  by_contra! h
  have hc : coc T.lab ((of a) ^ per a ω) ω = 1 := by
    rw [coc_pow_congr (lab' := fun _ _ ↦ (1 : FreeGroup T.Gens)) a _ ω
      (fun i hi ↦ T.lab_of_mem (h i hi))]
    exact coc_eq_one _ (fun _ _ ↦ rfl) _ _
  have h1 : T.rewrite (T.cj ((of a) ^ per a ω) ω) = 1 := by
    change coc T.lab ((T.t ((of a) ^ per a ω • ω))⁻¹ * (of a) ^ per a ω * T.t ω) ω₀ = 1
    have hi := coc_inv T.lab (T.t ω) ω₀
    rw [T.t_smul, T.coc_t, inv_one] at hi
    rw [pow_per_smul, coc_mul, coc_mul, T.coc_t, mul_one, T.t_smul, pow_per_smul, hi, one_mul,
      hc]
  have h2 := T.rewrite_injective (h1.trans (_root_.map_one _).symm)
  have h3 := congrArg Subtype.val h2
  simp only [cj, pow_per_smul, OneMemClass.coe_one] at h3
  have h4 : (of a) ^ per a ω = 1 := by
    have : (of a) ^ per a ω = T.t ω * ((T.t ω)⁻¹ * (of a) ^ per a ω * T.t ω) * (T.t ω)⁻¹ := by
      group
    rw [this, h3]; group
  exact of_pow_ne_one a (per_pos a ω) h4

/-- The chosen point of an `⟨a⟩`-orbit: the source of a non-tree edge with letter `a`. -/
noncomputable def chosen [Finite Ω] (a : α)
    (q : MulAction.orbitRel.Quotient (Subgroup.zpowers (of a)) Ω) : Ω :=
  (of a) ^ (Classical.choose (T.exists_notMem_E a q.out)) • q.out

lemma chosen_notMem [Finite Ω] (a : α) (q) : (T.chosen a q, a) ∉ T.E :=
  (Classical.choose_spec (T.exists_notMem_E a q.out)).2

lemma orb_chosen [Finite Ω] (a : α) (q) : orb a (T.chosen a q) = q := by
  rw [chosen, ← zpow_natCast, orb_zpow_smul]
  exact Quotient.out_eq q

variable [Finite Ω] (A : Finset α)

/-- The chosen edges: `(c, a)` with `a ∈ A` and `c` the chosen point of its `⟨a⟩`-orbit. -/
def IsChosen (e : Ω × α) : Prop := e.2 ∈ A ∧ e.1 = T.chosen e.2 (orb e.2 e.1)

lemma not_isChosen_of_mem {e : Ω × α} (he : e ∈ T.E) : ¬ T.IsChosen A e := by
  obtain ⟨ω, b⟩ := e
  rintro ⟨-, h⟩
  simp only at h
  rw [h] at he
  exact T.chosen_notMem _ _ he

/-- Only the chosen point itself carries the chosen edge of its orbit. -/
lemma not_isChosen_pow {a : α} {c : Ω} (hc : T.IsChosen A (c, a)) {i : ℕ} (hi0 : 0 < i)
    (hi : i < per a c) : ¬ T.IsChosen A ((of a) ^ i • c, a) := by
  rintro ⟨-, h⟩
  simp only at h
  have h' : (of a) ^ i • c = c := by
    rw [h, ← zpow_natCast, orb_zpow_smul]
    exact hc.2.symm
  have := Function.IsPeriodicPt.minimalPeriod_le hi0
    (MulAction.isPeriodicPt_smul_iff.mpr h')
  exact absurd hi (not_lt.mpr this)

/-- The generators of the quotient: non-tree edges that are not chosen. -/
abbrev Gens' := {e : T.Gens // ¬ T.IsChosen A e.1}

open scoped Classical in
/-- Labels: `1` on tree edges and chosen edges, the generator otherwise. -/
noncomputable def lab₀ (ω : Ω) (b : α) : FreeGroup (T.Gens' A) :=
  if h : (ω, b) ∈ T.E ∨ T.IsChosen A (ω, b) then 1 else
    of ⟨⟨(ω, b), fun h' ↦ h (Or.inl h')⟩, fun h' ↦ h (Or.inr h')⟩

open scoped Classical in
/-- The eliminating labels: on a chosen edge `(c, b)`, the inverse of the label of the rest of the
cusp loop. -/
noncomputable def lab' (ω : Ω) (b : α) : FreeGroup (T.Gens' A) :=
  if T.IsChosen A (ω, b) then (coc (T.lab₀ A) ((of b) ^ (per b ω - 1)) (of b • ω))⁻¹
  else T.lab₀ A ω b

lemma lab'_of_not {ω : Ω} {b : α} (h : ¬ T.IsChosen A (ω, b)) : T.lab' A ω b = T.lab₀ A ω b := by
  simp [lab', h]

lemma lab'_of_mem {e : Ω × α} (he : e ∈ T.E) : T.lab' A e.1 e.2 = 1 := by
  rw [lab'_of_not _ _ (T.not_isChosen_of_mem A he), lab₀, dif_pos (Or.inl he)]

lemma lab'_gens (e : T.Gens' A) : T.lab' A e.1.1.1 e.1.1.2 = of e := by
  rw [lab'_of_not _ _ e.2, lab₀, dif_neg]
  rintro (h | h)
  · exact e.1.2 h
  · exact e.2 h

lemma coc_lab'_rest {b : α} {c : Ω} (hc : T.IsChosen A (c, b)) :
    coc (T.lab' A) ((of b) ^ (per b c - 1)) (of b • c) =
      coc (T.lab₀ A) ((of b) ^ (per b c - 1)) (of b • c) := by
  apply coc_pow_congr
  intro i hi
  rw [← mul_smul, ← pow_succ]
  exact T.lab'_of_not A (T.not_isChosen_pow A hc (by omega) (by omega))

/-- The rewriting with the eliminating labels kills the cusp loop of a chosen point. -/
lemma coc_pow_per_chosen {b : α} {c : Ω} (hc : T.IsChosen A (c, b)) :
    coc (T.lab' A) ((of b) ^ per b c) c = 1 := by
  have hm := per_pos b c
  conv_lhs => rw [show per b c = (per b c - 1) + 1 by omega, pow_succ, coc_mul, coc_of]
  rw [T.coc_lab'_rest A hc, lab', if_pos hc, mul_inv_cancel]

/-- The rewriting with the eliminating labels kills every power `bᵏ` fixing a point, `b ∈ A`. -/
lemma coc_zpow_eq_one_of_smul {b : α} (hb : b ∈ A) {ω : Ω} {k : ℤ}
    (hk : (of b) ^ k • ω = ω) : coc (T.lab' A) ((of b) ^ k) ω = 1 := by
  set c := T.chosen b (orb b ω)
  have hc : T.IsChosen A (c, b) := ⟨hb, by simp only [c, T.orb_chosen]⟩
  obtain ⟨j, hj⟩ := orb_eq_iff.mp (T.orb_chosen b (orb b ω)).symm
  -- hj : (of b) ^ j • c = ω
  have hkc : (of b) ^ k • c = c := by
    have : (of b) ^ j • (of b) ^ k • c = (of b) ^ j • c := by
      rw [← mul_smul, ← zpow_add, add_comm, zpow_add, mul_smul, hj, hk]
    exact smul_left_cancel _ this
  have hck : coc (T.lab' A) ((of b) ^ k) c = 1 := by
    obtain ⟨l, rfl⟩ := MulAction.zpow_smul_eq_iff_minimalPeriod_dvd.mp hkc
    rw [zpow_mul, zpow_natCast]
    exact coc_zpow_eq_one (pow_per_smul b c) (T.coc_pow_per_chosen A hc) l
  have hcomm : (of b) ^ k = (of b) ^ j * (of b) ^ k * ((of b) ^ j)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← zpow_add, ← zpow_add, add_comm]
  rw [← hj, hcomm, coc_mul, coc_mul, inv_smul_smul, hkc, coc_inv, hck, mul_one, mul_inv_cancel]

/-- The eliminating rewriting `H → F(non-tree, non-chosen edges)`. -/
noncomputable def tau : MulAction.stabilizer (FreeGroup α) ω₀ →* FreeGroup (T.Gens' A) :=
  cocHom (T.lab' A) ω₀

lemma tau_basis (e : T.Gens' A) : T.tau A (T.basis e.1) = of e := by
  change coc (T.lab' A) (T.basis e.1 : FreeGroup α) ω₀ = of e
  rw [basis_apply, T.coc_schreierGen_of _ (fun e he ↦ T.lab'_of_mem A he), lab'_gens]

lemma tau_surjective : Function.Surjective (T.tau A) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← FreeGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨e, rfl⟩
  exact ⟨_, T.tau_basis A e⟩

lemma cuspSubgroup_le_ker : cuspSubgroup (A : Set α) ω₀ ≤ (T.tau A).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro h ⟨b, hb, g, k, hh⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  change coc (T.lab' A) (h : FreeGroup α) ω₀ = 1
  have hfix : (of b) ^ k • g⁻¹ • ω₀ = g⁻¹ • ω₀ := by
    have := MulAction.mem_stabilizer_iff.mp h.2
    rw [hh, mul_smul, mul_smul] at this
    rw [← smul_left_cancel_iff g, this, smul_inv_smul]
  have key : coc (T.lab' A) g⁻¹ ω₀ = (coc (T.lab' A) g (g⁻¹ • ω₀))⁻¹ := by
    have := coc_inv (T.lab' A) g (g⁻¹ • ω₀)
    rwa [smul_inv_smul] at this
  rw [hh, coc_mul, coc_mul, hfix, T.coc_zpow_eq_one_of_smul A hb hfix, mul_one, key,
    mul_inv_cancel]

/-- The map from the free group on the non-tree, non-chosen edges to the quotient. -/
noncomputable def psi : FreeGroup (T.Gens' A) →*
    MulAction.stabilizer (FreeGroup α) ω₀ ⧸ cuspSubgroup (A : Set α) ω₀ :=
  FreeGroup.lift fun e ↦ (T.basis e.1 : MulAction.stabilizer (FreeGroup α) ω₀)

lemma psi_lab'_of_not {ω : Ω} {b : α} (h : ¬ T.IsChosen A (ω, b)) :
    T.psi A (T.lab' A ω b) = (T.cj (of b) ω : _ ⧸ cuspSubgroup (A : Set α) ω₀) := by
  rw [T.lab'_of_not A h, lab₀]
  split_ifs with h'
  · rcases h' with h' | h'
    · have : T.cj (of b) ω = 1 := Subtype.ext (T.schreierGen_eq_one _ h')
      rw [this, _root_.map_one, QuotientGroup.mk_one]
    · exact absurd h' h
  · rw [psi, FreeGroup.lift_apply_of]
    congr 1
    exact Subtype.ext (T.basis_apply _)

lemma psi_coc_pow {b : α} (n : ℕ) (ω : Ω)
    (h : ∀ i < n, ¬ T.IsChosen A ((of b) ^ i • ω, b)) :
    T.psi A (coc (T.lab' A) ((of b) ^ n) ω) =
      (T.cj ((of b) ^ n) ω : _ ⧸ cuspSubgroup (A : Set α) ω₀) := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih =>
    have h0 := h 0 (by omega)
    rw [pow_zero, one_smul] at h0
    rw [pow_succ, coc_mul, T.cj_mul, _root_.map_mul, QuotientGroup.mk_mul, coc_of,
      T.psi_lab'_of_not A h0, ih]
    intro i hi
    have := h (i + 1) (by omega)
    rwa [pow_succ, mul_smul] at this

lemma psi_lab' (ω : Ω) (b : α) :
    T.psi A (T.lab' A ω b) = (T.cj (of b) ω : _ ⧸ cuspSubgroup (A : Set α) ω₀) := by
  by_cases hc : T.IsChosen A (ω, b)
  · have hm := per_pos b ω
    have hrest := T.psi_coc_pow A (b := b) (per b ω - 1) (of b • ω) (fun i hi ↦ by
      rw [← mul_smul, ← pow_succ]
      exact T.not_isChosen_pow A hc (by omega) (by omega))
    rw [lab', if_pos hc, _root_.map_inv, ← T.coc_lab'_rest A hc, hrest]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← QuotientGroup.mk_mul, ← T.cj_mul, ← pow_succ, show per b ω - 1 + 1 = per b ω by omega,
      QuotientGroup.eq_one_iff]
    refine Subgroup.subset_normalClosure ⟨b, hc.1, (T.t ω)⁻¹, per b ω, ?_⟩
    simp [cj, pow_per_smul]
  · exact T.psi_lab'_of_not A hc

lemma psi_coc (g : FreeGroup α) (ω : Ω) :
    T.psi A (coc (T.lab' A) g ω) = (T.cj g ω : _ ⧸ cuspSubgroup (A : Set α) ω₀) := by
  induction g using FreeGroup.induction_on generalizing ω with
  | C1 => simp
  | of b => rw [coc_of, psi_lab']
  | inv_of b _ =>
    obtain ⟨ω', rfl⟩ : ∃ ω', ω = of b • ω' := ⟨(of b)⁻¹ • ω, (smul_inv_smul _ _).symm⟩
    rw [coc_inv, _root_.map_inv, coc_of, psi_lab', T.cj_inv, QuotientGroup.mk_inv]
  | mul x y hx hy => rw [coc_mul, _root_.map_mul, hx, hy, T.cj_mul, QuotientGroup.mk_mul]

lemma psi_tau (h : MulAction.stabilizer (FreeGroup α) ω₀) :
    T.psi A (T.tau A h) = (h : _ ⧸ cuspSubgroup (A : Set α) ω₀) := by
  change T.psi A (coc (T.lab' A) (h : FreeGroup α) ω₀) = _
  rw [psi_coc, cj_of_stab]

lemma ker_tau : (T.tau A).ker = cuspSubgroup (A : Set α) ω₀ := by
  refine le_antisymm (fun h hh ↦ ?_) (T.cuspSubgroup_le_ker A)
  rw [MonoidHom.mem_ker] at hh
  have := T.psi_tau A h
  rw [hh, _root_.map_one] at this
  exact (QuotientGroup.eq_one_iff h).mp this.symm

/-- **Filling the cusps**: the quotient of the stabiliser by the cusp subgroup is free on the
non-tree, non-chosen edges. -/
noncomputable def quotientCuspEquiv :
    MulAction.stabilizer (FreeGroup α) ω₀ ⧸ cuspSubgroup (A : Set α) ω₀ ≃*
      FreeGroup (T.Gens' A) :=
  (QuotientGroup.quotientMulEquivOfEq (T.ker_tau A).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (T.tau_surjective A))

/-- The chosen edges are in bijection with the pairs (letter of `A`, orbit). -/
noncomputable def chosenEquiv :
    {e : T.Gens // T.IsChosen A e.1} ≃
      Σ a : A, MulAction.orbitRel.Quotient (Subgroup.zpowers (of (a : α))) Ω where
  toFun e := ⟨⟨e.1.1.2, e.2.1⟩, orb e.1.1.2 e.1.1.1⟩
  invFun p := ⟨⟨(T.chosen p.1 p.2, p.1), T.chosen_notMem _ _⟩, p.1.2, by
    simp only [T.orb_chosen]⟩
  left_inv e := by
    obtain ⟨⟨⟨ω, b⟩, he⟩, hb, hc⟩ := e
    simp only at hc
    ext <;> simp [← hc]
  right_inv p := by
    obtain ⟨a, q⟩ := p
    simp [T.orb_chosen]

lemma card_gens' [Finite α] :
    Nat.card (T.Gens' A) + ∑ a ∈ A,
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (of a)) Ω) = Nat.card T.Gens := by
  classical
  have h1 : Nat.card {e : T.Gens // T.IsChosen A e.1} =
      ∑ a ∈ A, Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (of a)) Ω) := by
    rw [Nat.card_congr (T.chosenEquiv A), Nat.card_sigma]
    exact Finset.sum_coe_sort A
      (fun a ↦ Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (of a)) Ω))
  have h2 := Nat.card_congr (Equiv.sumCompl fun e : T.Gens ↦ T.IsChosen A e.1)
  rw [Nat.card_sum] at h2
  have h3 : Nat.card (T.Gens' A) = Nat.card {e : T.Gens // ¬ T.IsChosen A e.1} := rfl
  omega

end Transversal

/-- **Filling cusps in a finite-index subgroup of a free group.** For a transitive action of
`F(α)` on a finite set `Ω` and a finite set `A` of letters, the quotient of the stabiliser of `ω₀`
by the cusp subgroup of `A` is free of rank `|Ω| (|α| - 1) + 1 - ∑_{a ∈ A} #(⟨a⟩-orbits)`. -/
theorem exists_quotient_cuspSubgroup_mulEquiv [Finite Ω] [Finite α] (A : Finset α) {ω₀ : Ω}
    (htrans : ∀ ω, ∃ g : FreeGroup α, g • ω₀ = ω) :
    ∃ (ι : Type (max u v)) (_ : Finite ι),
      Nonempty (MulAction.stabilizer (FreeGroup α) ω₀ ⧸ cuspSubgroup (A : Set α) ω₀ ≃*
        FreeGroup ι) ∧
      Nat.card ι + Nat.card Ω +
        ∑ a ∈ A, Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (of a)) Ω) =
        Nat.card Ω * Nat.card α + 1 := by
  set T := (Parent.bfs htrans).toTransversal
  refine ⟨T.Gens' A, inferInstance, ⟨T.quotientCuspEquiv A⟩, ?_⟩
  have h1 := T.card_gens' A
  have h2 : Nat.card T.Gens + Nat.card Ω = Nat.card Ω * Nat.card α + 1 :=
    (Parent.bfs htrans).card_gens
  omega

end Pi1.ReidemeisterSchreier
