/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Profinite.FiniteLifts
public import Pi1.Profinite.Completion
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Second cohomology with locally constant cochains and central extensions

For a topological group `G` acting on a commutative group `M` (written multiplicatively, no
topology on `M`) we define

`H2lc G M = Z²(G, M) / B²(G, M)`,

where `Z²(G, M)` is the group of *locally constant* functions `f : G × G → M` satisfying the
multiplicative 2-cocycle condition `groupCohomology.IsMulCocycle₂`, and `B²(G, M)` consists of
the cocycles `(g, h) ↦ g • x h / x (g * h) * x g` with `x : G → M` locally constant. For a
profinite `G` and a discrete `G`-module `M` this is the continuous cohomology `H²(G, M)` (cochains
`Gⁿ → M` continuous for the discrete topology on `M`). The definition (carrier sets,
cocycle and coboundary conditions) is literally the same as that of `ContH2` in the repository
`local-class-field-theory` (which depends on `pi1`, so it cannot be imported here).

For a *trivial* action we work with the **twisted product** `Twist f = M ×_f G` of a 2-cocycle
`f`: the central extension `1 → M → Twist f → G → 1` with multiplication
`(m, g)(n, h) = (m n f(g, h), g h)`.

## Main results

* `exists_openNormal_invariant`: a locally constant function `f : G × G → M` with `M` finite on a
  compact totally disconnected group is invariant under right multiplication by `U × U` for an
  open normal subgroup `U` (so cocycles are inflated from finite quotients).
* `Twist.isCoboundary_of_section`: if `s : G → Twist f̄` is a continuous homomorphism lifting a
  finite quotient map `G → Q` (for `f = f̄ ∘ (q × q)`), then `f` is a coboundary of a locally
  constant cochain.
* `H2lc.mem_coboundaries_of_hasFiniteLifts`, `H2lc.subsingleton_of_hasFiniteLifts`: if `G` is
  compact, totally disconnected and has finite lifts (finite embedding problems are solvable),
  then `H²(G, M) = 0` for every finite `M` with trivial action. In particular
  (`H2lc.subsingleton_of_isOpen_freeHat`) **open subgroups of free profinite groups have
  `H²(·, M) = 0`** ([NSW] (3.5.6), (3.5.15): free profinite groups are projective, `cd ≤ 1`).

[NSW] = Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic v2.3.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology groupCohomology Pointwise

universe u v

/-- Normalise an identity in a multiplicative commutative group (via `Additive` and `abel`). -/
macro "pi1_mul_abel" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
             abel))

namespace Pi1.Profinite

/-! ### Locally constant cohomology -/

namespace H2lc

section Defs

variable (G M : Type*) [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]

/-- The 2-coboundary `(g, h) ↦ g • x h / x (g * h) * x g` of a 1-cochain `x`. -/
def dx (x : G → M) : G × G → M := fun gh ↦ gh.1 • x gh.2 / x (gh.1 * gh.2) * x gh.1

/-- The subgroup of locally constant 2-cocycles `G × G → M`. -/
def cocycles : Subgroup (G × G → M) where
  carrier := {f | IsLocallyConstant f ∧ IsMulCocycle₂ f}
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨hf.mul hg, fun a b c ↦ ?_⟩
    simp only [Pi.mul_apply, smul_mul']
    calc f (a * b, c) * g (a * b, c) * (f (a, b) * g (a, b))
        = (f (a * b, c) * f (a, b)) * (g (a * b, c) * g (a, b)) := by pi1_mul_abel
      _ = (a • f (b, c) * f (a, b * c)) * (a • g (b, c) * g (a, b * c)) := by
          rw [hf' a b c, hg' a b c]
      _ = _ := by pi1_mul_abel
  one_mem' := ⟨IsLocallyConstant.const 1, fun a b c ↦ by simp⟩
  inv_mem' := by
    rintro f ⟨hf, hf'⟩
    refine ⟨hf.inv, fun a b c ↦ ?_⟩
    simp only [Pi.inv_apply, smul_inv', ← mul_inv, hf' a b c]

omit [TopologicalSpace G] in
lemma dx_mul (x y : G → M) : dx G M (x * y) = dx G M x * dx G M y := by
  ext ⟨g, h⟩
  simp only [dx, Pi.mul_apply, smul_mul']
  pi1_mul_abel

/-- The subgroup of coboundaries of locally constant 1-cochains. -/
def coboundaries : Subgroup (cocycles G M) where
  carrier := {f | ∃ x : G → M, IsLocallyConstant x ∧ dx G M x = f}
  mul_mem' := by
    rintro f g ⟨x, hx, hxf⟩ ⟨y, hy, hyg⟩
    exact ⟨x * y, hx.mul hy, by rw [dx_mul, hxf, hyg]; rfl⟩
  one_mem' := ⟨1, IsLocallyConstant.const 1, by ext; simp [dx]⟩
  inv_mem' := by
    rintro f ⟨x, hx, hxf⟩
    refine ⟨x⁻¹, hx.inv, ?_⟩
    rw [Subgroup.coe_inv, ← hxf]
    ext ⟨g, h⟩
    simp only [dx, Pi.inv_apply, smul_inv']
    pi1_mul_abel

end Defs

end H2lc

/-- **Second cohomology of `G` with values in `M`, computed with locally constant cochains.** -/
def H2lc (G M : Type*) [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M] :
    Type _ :=
  H2lc.cocycles G M ⧸ H2lc.coboundaries G M

instance (G M : Type*) [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M] :
    CommGroup (H2lc G M) :=
  inferInstanceAs (CommGroup (_ ⧸ _))

/-! ### Locally constant functions are inflated from finite quotients -/

/-- **Locally constant functions on `G × G` are inflated from a finite quotient**: for a compact
totally disconnected topological group `G`, a finite set `M` and a locally constant
`f : G × G → M`, there is an open normal subgroup `U` with `f (x u, y v) = f (x, y)` for all
`u, v ∈ U`. -/
theorem exists_openNormal_invariant {G M : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Finite M]
    {f : G × G → M} (hf : IsLocallyConstant f) :
    ∃ U : Subgroup G, U.Normal ∧ IsOpen (U : Set G) ∧
      ∀ x y u v, u ∈ U → v ∈ U → f (x * u, y * v) = f (x, y) := by
  have hK (m : M) : ∃ V ∈ 𝓝 (1 : G × G), f ⁻¹' {m} * V ⊆ f ⁻¹' {m} :=
    compact_open_separated_mul_right (hf.isClosed_fiber m).isCompact (hf.isOpen_fiber m)
      subset_rfl
  choose V hV hKV using hK
  have hV' : (⋂ m, V m) ∈ 𝓝 ((1 : G), (1 : G)) := Filter.iInter_mem.2 hV
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hV'
  obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := hV'
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_interior (s := t₁ ∩ t₂))
    (mem_interior_iff_mem_nhds.2 (Filter.inter_mem ht₁ ht₂))
  refine ⟨N.toSubgroup, inferInstance, N.isOpen, fun x y u v hu hv ↦ ?_⟩
  have huv : (u, v) ∈ ⋂ m, V m :=
    ht ⟨(interior_subset (hN hu)).1, (interior_subset (hN hv)).2⟩
  have := hKV (f (x, y)) (Set.mul_mem_mul (a := (x, y)) rfl (Set.mem_iInter.1 huv (f (x, y))))
  exact this

/-! ### Cocycles for the trivial action and twisted products -/

section Twist

variable (G M : Type*) [Group G] [CommGroup M]

/-- The 2-cocycles `G × G → M` for the **trivial** action: `f(ab, c) f(a, b) = f(b, c) f(a, bc)`
(no topological condition). -/
def TrivCocycle : Subgroup (G × G → M) where
  carrier := {f | ∀ a b c : G, f (a * b, c) * f (a, b) = f (b, c) * f (a, b * c)}
  mul_mem' := by
    intro f g hf hg a b c
    simp only [Pi.mul_apply]
    calc f (a * b, c) * g (a * b, c) * (f (a, b) * g (a, b))
        = (f (a * b, c) * f (a, b)) * (g (a * b, c) * g (a, b)) := by pi1_mul_abel
      _ = (f (b, c) * f (a, b * c)) * (g (b, c) * g (a, b * c)) := by rw [hf a b c, hg a b c]
      _ = _ := by pi1_mul_abel
  one_mem' := fun a b c ↦ by simp
  inv_mem' := by
    intro f hf a b c
    simp only [Pi.inv_apply, ← mul_inv, hf a b c]

variable {G M}

lemma TrivCocycle.cond {f : G × G → M} (hf : f ∈ TrivCocycle G M) (a b c : G) :
    f (a * b, c) * f (a, b) = f (b, c) * f (a, b * c) := hf a b c

lemma TrivCocycle.apply_one_left {f : G × G → M} (hf : f ∈ TrivCocycle G M) (b : G) :
    f (1, b) = f (1, 1) := by
  have := TrivCocycle.cond hf 1 1 b
  simp only [one_mul] at this
  exact (mul_left_cancel this).symm

lemma TrivCocycle.apply_one_right {f : G × G → M} (hf : f ∈ TrivCocycle G M) (a : G) :
    f (a, 1) = f (1, 1) := by
  have := TrivCocycle.cond hf a 1 1
  simp only [mul_one] at this
  exact mul_right_cancel this

/-- For a trivial action, the locally constant cocycles are trivial-action cocycles. -/
lemma mem_trivCocycle_of_mem_cocycles [TopologicalSpace G] [MulDistribMulAction G M]
    (htriv : ∀ (g : G) (m : M), g • m = m) {f : G × G → M} (hf : f ∈ H2lc.cocycles G M) :
    f ∈ TrivCocycle G M := fun a b c ↦ by
  have := hf.2 a b c
  rwa [htriv] at this

/-- **The twisted product** `M ×_f G` of a trivial-action 2-cocycle `f`: pairs `(m, g)` with
`(m, g)(n, h) = (m n f(g, h), g h)`; a central extension of `G` by `M`. -/
@[ext]
structure Twist (f : TrivCocycle G M) where
  /-- The `M`-component. -/
  m : M
  /-- The `G`-component. -/
  g : G

namespace Twist

variable {f : TrivCocycle G M}

instance : Mul (Twist f) := ⟨fun x y ↦ ⟨x.m * y.m * f.1 (x.g, y.g), x.g * y.g⟩⟩
instance : One (Twist f) := ⟨⟨(f.1 (1, 1))⁻¹, 1⟩⟩
instance : Inv (Twist f) := ⟨fun x ↦ ⟨x.m⁻¹ * (f.1 (x.g⁻¹, x.g))⁻¹ * (f.1 (1, 1))⁻¹, x.g⁻¹⟩⟩

@[simp] lemma mul_m (x y : Twist f) : (x * y).m = x.m * y.m * f.1 (x.g, y.g) := rfl
@[simp] lemma mul_g (x y : Twist f) : (x * y).g = x.g * y.g := rfl
@[simp] lemma one_m : (1 : Twist f).m = (f.1 (1, 1))⁻¹ := rfl
@[simp] lemma one_g : (1 : Twist f).g = 1 := rfl
lemma inv_m' (x : Twist f) : x⁻¹.m = x.m⁻¹ * (f.1 (x.g⁻¹, x.g))⁻¹ * (f.1 (1, 1))⁻¹ := rfl
@[simp] lemma inv_g' (x : Twist f) : x⁻¹.g = x.g⁻¹ := rfl

instance : Group (Twist f) := Group.ofLeftAxioms
  (fun x y z ↦ by
    ext
    · simp only [mul_m, mul_g]
      calc x.m * y.m * f.1 (x.g, y.g) * z.m * f.1 (x.g * y.g, z.g)
          = x.m * y.m * z.m * (f.1 (x.g * y.g, z.g) * f.1 (x.g, y.g)) := by pi1_mul_abel
        _ = x.m * y.m * z.m * (f.1 (y.g, z.g) * f.1 (x.g, y.g * z.g)) := by
            rw [TrivCocycle.cond f.2 x.g y.g z.g]
        _ = _ := by pi1_mul_abel
    · simp [mul_assoc])
  (fun x ↦ by
    ext
    · simp only [mul_m, one_m, one_g, TrivCocycle.apply_one_left f.2]
      pi1_mul_abel
    · simp)
  (fun x ↦ by
    ext
    · simp only [mul_m, inv_m', inv_g', one_m]
      pi1_mul_abel
    · simp)

/-- The projection `M ×_f G → G`. -/
def proj : Twist f →* G where
  toFun x := x.g
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma proj_apply (x : Twist f) : proj x = x.g := rfl

lemma proj_surjective : Function.Surjective (proj : Twist f →* G) :=
  fun g ↦ ⟨⟨1, g⟩, rfl⟩

/-- The inclusion `M → M ×_f G`, `m ↦ (m f(1,1)⁻¹, 1)`. -/
def incl : M →* Twist f where
  toFun c := ⟨c * (f.1 (1, 1))⁻¹, 1⟩
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp only [mul_m]
      pi1_mul_abel
    · simp

@[simp] lemma incl_m (c : M) : (incl c : Twist f).m = c * (f.1 (1, 1))⁻¹ := rfl
@[simp] lemma incl_g (c : M) : (incl c : Twist f).g = 1 := rfl

lemma incl_injective : Function.Injective (incl : M →* Twist f) := fun a b h ↦ by
  have := congrArg Twist.m h
  simpa using this

/-- The image of `M` is central. -/
lemma incl_mul_comm (c : M) (x : Twist f) : incl c * x = x * incl c := by
  ext
  · simp only [mul_m, incl_m, incl_g, TrivCocycle.apply_one_left f.2,
      TrivCocycle.apply_one_right f.2]
    pi1_mul_abel
  · simp

/-- An element over `1 ∈ G` is in the image of `M`. -/
lemma eq_incl_of_g_eq_one {x : Twist f} (hx : x.g = 1) : x = incl (x.m * f.1 (1, 1)) := by
  ext
  · simp
  · simp [hx]

/-- Two elements with the same image in `G` differ by an element of `M`. -/
lemma eq_mul_incl {x y : Twist f} (h : x.g = y.g) : y = x * incl (y.m / x.m) := by
  ext
  · rw [mul_m, incl_m, incl_g, TrivCocycle.apply_one_right f.2 x.g]
    pi1_mul_abel
  · rw [mul_g, incl_g, mul_one, h]

end Twist

/-- Commutators are unchanged by central factors. -/
lemma commutator_mul_central {E : Type*} [Group E] (x y a b : E) (ha : ∀ z, a * z = z * a)
    (hb : ∀ z, b * z = z * b) :
    x * a * (y * b) * (x * a)⁻¹ * (y * b)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  calc x * a * (y * b) * (x * a)⁻¹ * (y * b)⁻¹
      = a * (x * (y * b) * x⁻¹) * a⁻¹ * (y * b)⁻¹ := by rw [← ha x]; group
    _ = x * (y * b) * x⁻¹ * (y * b)⁻¹ := by rw [ha, mul_inv_cancel_right]
    _ = b * (x * y * x⁻¹ * y⁻¹) * b⁻¹ := by
        rw [← hb y]
        calc x * (b * y) * x⁻¹ * (b * y)⁻¹ = (x * b) * y * x⁻¹ * y⁻¹ * b⁻¹ := by group
          _ = (b * x) * y * x⁻¹ * y⁻¹ * b⁻¹ := by rw [hb x]
          _ = _ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hb, mul_inv_cancel_right]

namespace Twist

variable {f : TrivCocycle G M}

/-- In `M ×_f G` the commutator of two elements only depends on their images in `G`. -/
lemma commutator_eq_of_g_eq {x x' y y' : Twist f} (hx : x.g = x'.g) (hy : y.g = y'.g) :
    x' * y' * x'⁻¹ * y'⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  rw [eq_mul_incl hx, eq_mul_incl hy]
  exact commutator_mul_central _ _ _ _ (incl_mul_comm _) (incl_mul_comm _)

end Twist

/-- **Sections give coboundaries.** Let `q : G →* Q` be a homomorphism and `f̄` a trivial-action
cocycle on `Q`. If `s : G →* Twist f̄` lifts `q` and has open fibres, then
`f̄ ∘ (q × q)` is the coboundary `(γ, δ) ↦ x δ / x (γ δ) * x γ` of the locally constant
`x = (s ·).m⁻¹`. -/
theorem Twist.exists_of_section [TopologicalSpace G] {Q : Type*} [Group Q] (q : G →* Q)
    {f : TrivCocycle Q M} (s : G →* Twist f) (hs : ∀ e, IsOpen (s ⁻¹' {e}))
    (hsq : ∀ γ, (s γ).g = q γ) :
    ∃ x : G → M, IsLocallyConstant x ∧
      ∀ γ δ, f.1 (q γ, q δ) = x δ / x (γ * δ) * x γ := by
  refine ⟨fun γ ↦ (s γ).m⁻¹, ?_, fun γ δ ↦ ?_⟩
  · rw [IsLocallyConstant.iff_isOpen_fiber]
    intro c
    have : (fun γ ↦ (s γ).m⁻¹) ⁻¹' {c} = ⋃ e ∈ {e : Twist f | e.m⁻¹ = c}, s ⁻¹' {e} := by
      ext γ
      simp
    rw [this]
    exact isOpen_biUnion fun e _ ↦ hs e
  · have h := congrArg Twist.m (map_mul s γ δ)
    rw [Twist.mul_m, hsq, hsq] at h
    simp only [h]
    pi1_mul_abel

end Twist

/-! ### Groups with finite lifts have trivial `H²` -/

namespace H2lc

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {M : Type u} [CommGroup M] [Finite M] [MulDistribMulAction G M]

omit [MulDistribMulAction G M] in
/-- **Locally constant trivial-action cocycles are inflated from finite quotients**: there are an
open normal subgroup `U` and a cocycle `F` on the finite group `G ⧸ U` with
`f (x, y) = F (x U, y U)`. -/
theorem _root_.Pi1.Profinite.TrivCocycle.exists_inflation {f : G × G → M}
    (hf : f ∈ TrivCocycle G M) (hlc : IsLocallyConstant f) :
    ∃ (U : Subgroup G) (_ : U.Normal), IsOpen (U : Set G) ∧
      ∃ F : TrivCocycle (G ⧸ U) M, ∀ x y : G, F.1 ((x : G ⧸ U), (y : G ⧸ U)) = f (x, y) := by
  classical
  obtain ⟨U, hUn, hUo, hU⟩ := exists_openNormal_invariant hlc
  refine ⟨U, hUn, hUo, ?_⟩
  let q : G →* G ⧸ U := QuotientGroup.mk' U
  let fbar : (G ⧸ U) × (G ⧸ U) → M := fun p ↦ f (p.1.out, p.2.out)
  have hfbar (x y : G) : fbar (q x, q y) = f (x, y) := by
    have hx : x⁻¹ * (q x).out ∈ U := QuotientGroup.leftRel_apply.1
      (Quotient.exact (Quotient.out_eq (q x)).symm)
    have hy : y⁻¹ * (q y).out ∈ U := QuotientGroup.leftRel_apply.1
      (Quotient.exact (Quotient.out_eq (q y)).symm)
    have := hU x y _ _ hx hy
    simp only [mul_inv_cancel_left] at this
    exact this
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective U
  refine ⟨⟨fbar, fun a b c ↦ ?_⟩, hfbar⟩
  obtain ⟨x, rfl⟩ := hq a
  obtain ⟨y, rfl⟩ := hq b
  obtain ⟨z, rfl⟩ := hq c
  simp only [← map_mul, hfbar]
  exact TrivCocycle.cond hf x y z

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Finite M]
  [MulDistribMulAction G M] in
lemma _root_.Pi1.Profinite.Twist.finite {Q : Type*} [Group Q] [Finite Q] [Finite M]
    (F : TrivCocycle Q M) : Finite (Twist F) :=
  Finite.of_injective (fun e : Twist F ↦ (e.m, e.g)) fun a b h ↦ by
    simp only [Prod.mk.injEq] at h
    exact Twist.ext h.1 h.2

omit [CompactSpace G] [TotallyDisconnectedSpace G] [Finite M] [MulDistribMulAction G M] in
lemma isOpen_mk_fiber (U : Subgroup G) [U.Normal] (hU : IsOpen (U : Set G)) (a : G ⧸ U) :
    IsOpen ((QuotientGroup.mk' U) ⁻¹' {a}) := by
  convert isOpen_setOf_mk_eq U hU (Quotient.out a) using 1
  ext y
  simp

/-- **If finite embedding problems for `G` are solvable, every locally constant 2-cocycle with
values in a finite trivial `G`-module is a coboundary** (`H²(G, M) = 0`; cf. [NSW] (3.5.6)). -/
theorem mem_coboundaries_of_hasFiniteLifts (hG : HasFiniteLifts.{u} G)
    (htriv : ∀ (g : G) (m : M), g • m = m) (f : cocycles G M) : f ∈ coboundaries G M := by
  obtain ⟨U, hUn, hUo, F, hF⟩ := TrivCocycle.exists_inflation
    (mem_trivCocycle_of_mem_cocycles htriv f.2) f.2.1
  haveI : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hUo
  haveI := Twist.finite F
  let q : G →* G ⧸ U := QuotientGroup.mk' U
  obtain ⟨s, hs, hsq⟩ := hG (Twist F) (G ⧸ U) Twist.proj Twist.proj_surjective q
    (isOpen_mk_fiber U hUo)
  obtain ⟨x, hx, hxf⟩ := Twist.exists_of_section q s hs fun γ ↦ DFunLike.congr_fun hsq γ
  refine ⟨x, hx, ?_⟩
  ext ⟨γ, δ⟩
  rw [← hF, show ((γ : G ⧸ U), (δ : G ⧸ U)) = (q γ, q δ) from rfl, hxf]
  simp [dx, htriv]

/-- **`H²(G, M) = 0`** for `G` compact, totally disconnected, with finite lifts, and `M` finite
with trivial action. -/
theorem subsingleton_of_hasFiniteLifts (hG : HasFiniteLifts.{u} G)
    (htriv : ∀ (g : G) (m : M), g • m = m) : Subsingleton (H2lc G M) := by
  refine ⟨fun a b ↦ ?_⟩
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  change (QuotientGroup.mk a : cocycles G M ⧸ coboundaries G M) = QuotientGroup.mk b
  rw [QuotientGroup.eq]
  exact mem_coboundaries_of_hasFiniteLifts hG htriv _

end H2lc

/-- **Open subgroups of free profinite groups have `H²(·, M) = 0`** for finite trivial `M`. -/
theorem H2lc.subsingleton_of_isOpen_freeHat {α : Type u} (H : Subgroup (FreeHat α))
    (hH : IsOpen (H : Set (FreeHat α))) {M : Type u} [CommGroup M] [Finite M]
    [MulDistribMulAction H M] (htriv : ∀ (g : H) (m : M), g • m = m) :
    Subsingleton (H2lc H M) :=
  haveI : CompactSpace H := isCompact_iff_compactSpace.1
    (Subgroup.isClosed_of_isOpen H hH).isCompact
  H2lc.subsingleton_of_hasFiniteLifts (FreeHat.hasFiniteLifts_of_isOpen α H hH) htriv

end Pi1.Profinite
