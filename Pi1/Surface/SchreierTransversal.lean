/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.ReidemeisterSchreier
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group

/-!
# Existence of Schreier transversals and the Schreier index formula

For a transitive action of `F(α)` on `Ω` we build a Schreier transversal from a breadth-first
search (`Pi1.ReidemeisterSchreier.Parent.bfs`): the depth of `ω` is the least number of letters
needed to reach it from `ω₀`, and each `ω ≠ ω₀` gets one *parent edge* to a vertex of smaller
depth. The words `t ω` are read off along parent edges (`Parent.t`, by well-founded recursion on
the depth) and the tree edges are the parent edges (`Parent.toTransversal`).

Parent edges of distinct vertices are distinct, so for finite `Ω` and `α` there are `|Ω| - 1`
tree edges and the Schreier basis of the stabiliser has `|Ω| (|α| - 1) + 1` elements
(`Parent.card_gens`: `|Gens| + |Ω| = |Ω| |α| + 1`), Schreier's index formula
(Magnus–Karrass–Solitar, *Combinatorial Group Theory*, Thm. 2.10; Lyndon–Schupp, Ch. I,
Prop. 3.9).

## Main declarations

* `Pi1.ReidemeisterSchreier.Parent`: depth function and parent edges;
* `Parent.toTransversal`: the associated Schreier transversal;
* `Parent.bfs`: parent data for a transitive action;
* `Parent.card_gens`, `exists_transversal_card`.
-/

@[expose] public section

namespace Pi1.ReidemeisterSchreier

open FreeGroup

variable {α Ω : Type*} [MulAction (FreeGroup α) Ω]

variable (α) in
/-- Parent data: a depth function and, for every `ω ≠ ω₀`, an edge joining `ω` to a vertex of
smaller depth (either `ω → a • ω` or `ω' → a • ω' = ω`). -/
structure Parent (ω₀ : Ω) where
  /-- The depth. -/
  depth : Ω → ℕ
  /-- The parent edge of `ω ≠ ω₀`. -/
  edge : ∀ ω, ω ≠ ω₀ → Ω × α
  edge_spec : ∀ ω (h : ω ≠ ω₀),
    ((edge ω h).1 = ω ∧ depth (of (edge ω h).2 • ω) < depth ω) ∨
      (of (edge ω h).2 • (edge ω h).1 = ω ∧ depth (edge ω h).1 < depth ω)

namespace Parent

variable {ω₀ : Ω} (P : Parent α ω₀)

set_option linter.unusedVariables false in
open scoped Classical in
/-- The coset representatives along parent edges. -/
noncomputable def t (ω : Ω) : FreeGroup α :=
  if h : ω = ω₀ then 1 else
    if h' : (P.edge ω h).1 = ω ∧ P.depth (of (P.edge ω h).2 • ω) < P.depth ω then
      (of (P.edge ω h).2)⁻¹ * t (of (P.edge ω h).2 • ω)
    else of (P.edge ω h).2 * t (P.edge ω h).1
termination_by P.depth ω
decreasing_by
  · exact h'.2
  · exact ((P.edge_spec ω h).resolve_left h').2

lemma t_base : P.t ω₀ = 1 := by
  rw [t, dif_pos rfl]

lemma t_of_first {ω : Ω} (h : ω ≠ ω₀)
    (h' : (P.edge ω h).1 = ω ∧ P.depth (of (P.edge ω h).2 • ω) < P.depth ω) :
    P.t ω = (of (P.edge ω h).2)⁻¹ * P.t (of (P.edge ω h).2 • ω) := by
  rw [t, dif_neg h, dif_pos h']

lemma t_of_second {ω : Ω} (h : ω ≠ ω₀)
    (h' : ¬ ((P.edge ω h).1 = ω ∧ P.depth (of (P.edge ω h).2 • ω) < P.depth ω)) :
    P.t ω = of (P.edge ω h).2 * P.t (P.edge ω h).1 := by
  rw [t, dif_neg h, dif_neg h']

lemma t_smul (ω : Ω) : P.t ω • ω₀ = ω := by
  induction hd : P.depth ω using Nat.strong_induction_on generalizing ω with
  | _ n ih =>
    by_cases h : ω = ω₀
    · subst h; rw [P.t_base, one_smul]
    by_cases h' : (P.edge ω h).1 = ω ∧ P.depth (of (P.edge ω h).2 • ω) < P.depth ω
    · rw [P.t_of_first h h', mul_smul, ih _ (hd ▸ h'.2) _ rfl, inv_smul_smul]
    · have h2 := (P.edge_spec ω h).resolve_left h'
      rw [P.t_of_second h h', mul_smul, ih _ (hd ▸ h2.2) _ rfl, h2.1]

/-- The tree edges: the parent edges. -/
def E : Set (Ω × α) := {e | ∃ ω h, P.edge ω h = e}

lemma schreierGen_edge (ω : Ω) (h : ω ≠ ω₀) :
    schreierGen P.t (P.edge ω h).1 (P.edge ω h).2 = 1 := by
  by_cases h' : (P.edge ω h).1 = ω ∧ P.depth (of (P.edge ω h).2 • ω) < P.depth ω
  · rw [schreierGen, h'.1, P.t_of_first h h']
    group
  · have h2 := (P.edge_spec ω h).resolve_left h'
    rw [schreierGen, h2.1, P.t_of_second h h']
    group

/-- The Schreier transversal of parent data. -/
noncomputable def toTransversal : Transversal α ω₀ where
  t := P.t
  E := P.E
  t_smul := P.t_smul
  t_base := P.t_base
  schreierGen_eq_one := by
    rintro _ ⟨ω, h, rfl⟩
    exact P.schreierGen_edge ω h
  depth := P.depth
  exists_edge ω h := ⟨P.edge ω h, ⟨ω, h, rfl⟩, P.edge_spec ω h⟩

lemma edge_injective :
    Function.Injective fun ω : {ω : Ω // ω ≠ ω₀} ↦ P.edge ω.1 ω.2 := by
  rintro ⟨ω, h⟩ ⟨ω', h'⟩ he
  simp only at he
  have s := P.edge_spec ω h
  have s' := P.edge_spec ω' h'
  rw [he] at s
  apply Subtype.ext
  simp only
  generalize P.edge ω' h' = e at s s'
  obtain ⟨u, a⟩ := e
  simp only at s s'
  rcases s with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ <;> rcases s' with ⟨rfl, hs'⟩ | ⟨rfl, hs'⟩
  · rfl
  · omega
  · omega
  · rfl

lemma card_E [Finite Ω] : Nat.card P.E + 1 = Nat.card Ω := by
  have hE : Set.range (fun ω : {ω : Ω // ω ≠ ω₀} ↦ P.edge ω.1 ω.2) = P.E := by
    ext e
    simp [E]
  have h1 : Nat.card P.E = Nat.card {ω : Ω // ω ≠ ω₀} := by
    rw [← hE]; exact (Nat.card_congr (Equiv.ofInjective _ P.edge_injective)).symm
  have h2 := Set.ncard_add_ncard_compl ({ω₀} : Set Ω)
  rw [Set.ncard_singleton] at h2
  have h3 : Nat.card {ω : Ω // ω ≠ ω₀} = ({ω₀}ᶜ : Set Ω).ncard :=
    Nat.card_coe_set_eq ({ω₀}ᶜ : Set Ω)
  omega

/-- **Schreier's index formula** for the transversal of parent data: the Schreier basis of the
stabiliser has `|Ω| (|α| - 1) + 1` elements. -/
lemma card_gens [Finite Ω] [Finite α] :
    Nat.card P.toTransversal.Gens + Nat.card Ω = Nat.card Ω * Nat.card α + 1 := by
  have h1 := Set.ncard_add_ncard_compl P.E
  rw [Nat.card_prod] at h1
  have h2 : Nat.card P.toTransversal.Gens = (P.Eᶜ : Set (Ω × α)).ncard :=
    Nat.card_coe_set_eq (P.Eᶜ : Set (Ω × α))
  have h3 : Nat.card P.E = P.E.ncard := Nat.card_coe_set_eq P.E
  have h4 := P.card_E
  omega

/-! ### Breadth-first search -/

variable (α) in
/-- `Reach α ω₀ n ω`: `ω` is reached from `ω₀` by a path of at most `n` edges. -/
def Reach (ω₀ : Ω) : ℕ → Ω → Prop
  | 0, ω => ω = ω₀
  | n + 1, ω => Reach ω₀ n ω ∨ ∃ a : α, Reach ω₀ n ((of a)⁻¹ • ω) ∨ Reach ω₀ n (of a • ω)

lemma exists_reach (htrans : ∀ ω, ∃ g : FreeGroup α, g • ω₀ = ω) (ω : Ω) :
    ∃ n, Reach α ω₀ n ω := by
  have key : ∀ (g : FreeGroup α) (ω : Ω), (∃ n, Reach α ω₀ n ω) → ∃ n, Reach α ω₀ n (g • ω) := by
    intro g
    induction g using FreeGroup.induction_on with
    | C1 => simp
    | of a =>
      rintro ω ⟨n, hn⟩
      exact ⟨n + 1, Or.inr ⟨a, Or.inl (by rwa [inv_smul_smul])⟩⟩
    | inv_of a _ =>
      rintro ω ⟨n, hn⟩
      exact ⟨n + 1, Or.inr ⟨a, Or.inr (by rwa [smul_inv_smul])⟩⟩
    | mul x y hx hy =>
      intro ω h
      rw [mul_smul]
      exact hx _ (hy _ h)
  obtain ⟨g, rfl⟩ := htrans ω
  exact key g ω₀ ⟨0, rfl⟩

open scoped Classical in
/-- The breadth-first depth: the least number of edges from `ω₀`. -/
noncomputable def bfsDepth (htrans : ∀ ω, ∃ g : FreeGroup α, g • ω₀ = ω) (ω : Ω) : ℕ :=
  Nat.find (exists_reach htrans ω)

lemma bfs_exists_edge (htrans : ∀ ω, ∃ g : FreeGroup α, g • ω₀ = ω) (ω : Ω) (h : ω ≠ ω₀) :
    ∃ e : Ω × α, (e.1 = ω ∧ bfsDepth htrans (of e.2 • ω) < bfsDepth htrans ω) ∨
      (of e.2 • e.1 = ω ∧ bfsDepth htrans e.1 < bfsDepth htrans ω) := by
  classical
  have hspec := Nat.find_spec (exists_reach htrans ω)
  change Reach α ω₀ (bfsDepth htrans ω) ω at hspec
  have hne : bfsDepth htrans ω ≠ 0 := by
    intro h0
    rw [h0] at hspec
    exact h hspec
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin : ¬ Reach α ω₀ k ω := Nat.find_min (exists_reach htrans ω) (by
    change k < bfsDepth htrans ω; omega)
  rw [hk] at hspec
  obtain hspec | ⟨a, ha | ha⟩ := hspec
  · exact absurd hspec hmin
  · refine ⟨((of a)⁻¹ • ω, a), Or.inr ⟨smul_inv_smul _ _, ?_⟩⟩
    have : bfsDepth htrans ((of a)⁻¹ • ω) ≤ k := Nat.find_le ha
    dsimp only
    omega
  · refine ⟨(ω, a), Or.inl ⟨rfl, ?_⟩⟩
    have : bfsDepth htrans (of a • ω) ≤ k := Nat.find_le ha
    dsimp only
    omega

/-- Parent data of a transitive action, by breadth-first search. -/
noncomputable def bfs (htrans : ∀ ω, ∃ g : FreeGroup α, g • ω₀ = ω) : Parent α ω₀ where
  depth := bfsDepth htrans
  edge ω h := Classical.choose (bfs_exists_edge htrans ω h)
  edge_spec ω h := Classical.choose_spec (bfs_exists_edge htrans ω h)

end Parent

/-- **Reidemeister–Schreier with Schreier's index formula**: for a transitive action of `F(α)` on
a finite set `Ω` there is a Schreier transversal whose basis of the stabiliser has
`|Ω| (|α| - 1) + 1` elements. -/
theorem exists_transversal_card [Finite Ω] [Finite α] {ω₀ : Ω}
    (htrans : ∀ ω, ∃ g : FreeGroup α, g • ω₀ = ω) :
    ∃ T : Transversal α ω₀, Nat.card T.Gens + Nat.card Ω = Nat.card Ω * Nat.card α + 1 :=
  ⟨(Parent.bfs htrans).toTransversal, (Parent.bfs htrans).card_gens⟩

end Pi1.ReidemeisterSchreier
