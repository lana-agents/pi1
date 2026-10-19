/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Profinite.H2
public import Pi1.Surface.FiniteLifts

/-!
# `H²` of the profinite surface group of a proper curve

For `g ≥ 1` and a finite commutative group `M` with trivial action, we prove

`H²(Π̂_{g,0}, M) ≅ M`   (`Pi1.SurfaceGroup.h2Equiv`),

with `H²` computed by locally constant cochains (`Pi1.Profinite.H2lc`, the continuous cohomology
with discrete coefficients). In particular `H²(Π̂_{g,0}, ℤ/n) ≅ ℤ/n` and
`H²(Π̂_{g,0}, μ_n) ≅ μ_n` for the geometric fundamental group `Δ_X ≅ Π̂_{g,0}` of a proper curve
of genus `g ≥ 1` in characteristic `0` (where `Δ_X` acts trivially on `μ_n`). By contrast, open
subgroups of free profinite groups have `H² = 0`
(`Pi1.Profinite.H2lc.subsingleton_of_isOpen_freeHat`).
Background: the pro-`p` completion of the fundamental group of a compact Riemann surface is a
Poincaré group ([NSW] III §7, p. 210); the presentation `Π_{g,n} = ⟨x₁, …, x_{2g}, y₁, …, yₙ |
(x₁, x₂) ⋯ (x_{2g−1}, x_{2g}) y₁ ⋯ yₙ = 1⟩` is [NSW] X §1 (p. 610). The proof below is
self-contained. [NSW] = Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., v2.3.

## The relator value

For a trivial-action 2-cocycle `f` of a group `G` and families `A, B : Fin g → G` with
`∏ᵢ [Aᵢ, Bᵢ] = 1`, the **relator value** `relVal A B f ∈ M` is defined by
`∏ᵢ [Âᵢ, B̂ᵢ] = ι(relVal A B f)` in the central extension `1 → M → M ×_f G → G → 1`, for any lifts
`Âᵢ, B̂ᵢ` of `Aᵢ, Bᵢ` (it does not depend on the lifts, `commProd_eq_incl_relVal`). It is
multiplicative in `f` (`relVal_mul`, via the Baer sum), natural in `G` (`relVal_comap`) and in `M`
(`relVal_map`), and kills coboundaries (`relVal_dx`). For `G = Π̂_{g,0}` and the images of the
standard generators:

* `relVal f = 1` implies that `f` is a coboundary of a locally constant cochain
  (`SurfaceGroup.exists_of_relVal_eq_one`): the cocycle is inflated from a finite quotient `Q`
  (`TrivCocycle.exists_inflation`), the lifts `(1, aᵢ), (1, bᵢ)` satisfy the surface relation
  in `M ×_f Q`, so define a homomorphism `Π_{g,0} → M ×_f Q`, which extends to `Π̂_{g,0}` and
  splits the extension;
* every `c ∈ M` is a relator value (`SurfaceGroup.exists_relVal_eq`), of the Heisenberg cocycle
  `(γ, δ) ↦ c ^ (α(γ) β(δ))` for the characters `α, β : Π̂_{g,0} → ℤ/|M|` dual to `a₁, b₁`.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology

universe u

namespace Pi1

open SurfaceGen

namespace Profinite

/-! ### The relator value of a cocycle -/

section RelVal

variable {G G' M M' : Type*} [Group G] [Group G'] [CommGroup M] [CommGroup M'] {n : ℕ}

/-- In a commutative group every product of commutators is trivial. -/
lemma commProd_eq_one_of_comm {C : Type*} [CommGroup C] (x y : Fin n → C) : commProd x y = 1 :=
  List.prod_eq_one fun z hz ↦ by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
    pi1_mul_abel

/-- **The relator value** of a trivial-action cocycle `f` at families `A, B : Fin n → G`:
`∏ᵢ [(1, Aᵢ), (1, Bᵢ)] = ι (relVal A B f)` in `M ×_f G` (when `∏ᵢ [Aᵢ, Bᵢ] = 1`). -/
def relVal (A B : Fin n → G) (f : TrivCocycle G M) : M :=
  (commProd (fun i ↦ (⟨1, A i⟩ : Twist f)) (fun i ↦ ⟨1, B i⟩)).m * f.1 (1, 1)

lemma Twist.commProd_g {f : TrivCocycle G M} (X Y : Fin n → Twist f) :
    (commProd X Y).g = commProd (fun i ↦ (X i).g) (fun i ↦ (Y i).g) :=
  map_commProd Twist.proj X Y

/-- **The relator value does not depend on the lifts**: for any lifts `Xᵢ, Yᵢ` of `Aᵢ, Bᵢ`,
`∏ᵢ [Xᵢ, Yᵢ] = ι (relVal A B f)`. -/
theorem commProd_eq_incl_relVal {A B : Fin n → G} (hAB : commProd A B = 1) (f : TrivCocycle G M)
    (X Y : Fin n → Twist f) (hX : ∀ i, (X i).g = A i) (hY : ∀ i, (Y i).g = B i) :
    commProd X Y = Twist.incl (relVal A B f) := by
  have h1 : commProd X Y = commProd (fun i ↦ (⟨1, A i⟩ : Twist f)) (fun i ↦ ⟨1, B i⟩) := by
    unfold commProd
    congr 2
    funext i
    exact Twist.commutator_eq_of_g_eq (hX i).symm (hY i).symm
  rw [h1]
  exact Twist.eq_incl_of_g_eq_one (by rw [Twist.commProd_g]; exact hAB)

/-- **The relator value is multiplicative in the cocycle** (Baer sum). -/
theorem relVal_mul {A B : Fin n → G} (hAB : commProd A B = 1) (f₁ f₂ : TrivCocycle G M) :
    relVal A B (f₁ * f₂) = relVal A B f₁ * relVal A B f₂ := by
  let S : Subgroup (Twist f₁ × Twist f₂) :=
    MonoidHom.eqLocus (Twist.proj.comp (MonoidHom.fst _ _)) (Twist.proj.comp (MonoidHom.snd _ _))
  have hS (x : S) : x.1.1.g = x.1.2.g := x.2
  let Ψ : S →* Twist (f₁ * f₂) :=
    { toFun := fun x ↦ ⟨x.1.1.m * x.1.2.m, x.1.1.g⟩
      map_one' := by
        ext
        · change (f₁.1 (1, 1))⁻¹ * (f₂.1 (1, 1))⁻¹ = ((f₁.1 * f₂.1) (1, 1))⁻¹
          rw [Pi.mul_apply, mul_inv]
        · rfl
      map_mul' := fun x y ↦ by
        ext
        · change x.1.1.m * y.1.1.m * f₁.1 (x.1.1.g, y.1.1.g) *
              (x.1.2.m * y.1.2.m * f₂.1 (x.1.2.g, y.1.2.g)) =
            x.1.1.m * x.1.2.m * (y.1.1.m * y.1.2.m) * (f₁.1 * f₂.1) (x.1.1.g, y.1.1.g)
          rw [hS x, hS y, Pi.mul_apply]
          pi1_mul_abel
        · rfl }
  let LA : Fin n → S := fun i ↦ ⟨(⟨1, A i⟩, ⟨1, A i⟩), rfl⟩
  let LB : Fin n → S := fun i ↦ ⟨(⟨1, B i⟩, ⟨1, B i⟩), rfl⟩
  have h12 : Ψ (commProd LA LB) = Twist.incl (relVal A B (f₁ * f₂)) := by
    rw [map_commProd]
    exact commProd_eq_incl_relVal hAB _ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
  have h1 : ((commProd LA LB : S) : Twist f₁ × Twist f₂).1 = Twist.incl (relVal A B f₁) := by
    have := map_commProd ((MonoidHom.fst _ _).comp S.subtype) LA LB
    exact this.trans (commProd_eq_incl_relVal hAB _ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl))
  have h2 : ((commProd LA LB : S) : Twist f₁ × Twist f₂).2 = Twist.incl (relVal A B f₂) := by
    have := map_commProd ((MonoidHom.snd _ _).comp S.subtype) LA LB
    exact this.trans (commProd_eq_incl_relVal hAB _ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl))
  have e := congrArg Twist.m h12
  change ((commProd LA LB : S) : Twist f₁ × Twist f₂).1.m *
      ((commProd LA LB : S) : Twist f₁ × Twist f₂).2.m = _ at e
  rw [h1, h2, Twist.incl_m, Twist.incl_m, Twist.incl_m] at e
  have : relVal A B (f₁ * f₂) = relVal A B f₁ * (f₁.1 (1, 1))⁻¹ *
      (relVal A B f₂ * (f₂.1 (1, 1))⁻¹) * ((f₁ * f₂).1 (1, 1)) := by
    rw [e]
    group
  rw [this, Subgroup.coe_mul, Pi.mul_apply]
  pi1_mul_abel

/-- Pulling back a trivial-action cocycle along a homomorphism. -/
lemma TrivCocycle.comap_mem (φ : G →* G') {f : G' × G' → M} (hf : f ∈ TrivCocycle G' M) :
    f ∘ Prod.map φ φ ∈ TrivCocycle G M := fun a b c ↦ by
  simpa [map_mul] using TrivCocycle.cond hf (φ a) (φ b) (φ c)

/-- **Naturality of the relator value in the group.** -/
theorem relVal_comap (φ : G →* G') {A B : Fin n → G} (hAB : commProd A B = 1)
    (f : TrivCocycle G' M) :
    relVal A B ⟨_, TrivCocycle.comap_mem φ f.2⟩ = relVal (fun i ↦ φ (A i)) (fun i ↦ φ (B i)) f := by
  set f' : TrivCocycle G M := ⟨_, TrivCocycle.comap_mem φ f.2⟩
  let τ : Twist f' →* Twist f :=
    { toFun := fun x ↦ ⟨x.m, φ x.g⟩
      map_one' := by
        ext
        · change (f.1 (φ 1, φ 1))⁻¹ = (f.1 (1, 1))⁻¹
          rw [map_one]
        · exact map_one φ
      map_mul' := fun x y ↦ by
        ext
        · rfl
        · exact map_mul φ _ _ }
  have hτ (c : M) : τ (Twist.incl c) = Twist.incl c := by
    ext
    · change c * (f.1 (φ 1, φ 1))⁻¹ = c * (f.1 (1, 1))⁻¹
      rw [map_one]
    · exact map_one φ
  have hAB' : commProd (fun i ↦ φ (A i)) (fun i ↦ φ (B i)) = 1 := by
    rw [← map_commProd, hAB, map_one]
  apply Twist.incl_injective (f := f)
  rw [← hτ, ← commProd_eq_incl_relVal hAB f' (fun i ↦ ⟨1, A i⟩) (fun i ↦ ⟨1, B i⟩)
    (fun _ ↦ rfl) (fun _ ↦ rfl), map_commProd]
  exact commProd_eq_incl_relVal hAB' f _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- Pushing a trivial-action cocycle forward along a homomorphism of coefficients. -/
lemma TrivCocycle.map_mem (ρ : M →* M') {f : G × G → M} (hf : f ∈ TrivCocycle G M) :
    ρ ∘ f ∈ TrivCocycle G M' := fun a b c ↦ by
  simpa [map_mul] using congrArg ρ (TrivCocycle.cond hf a b c)

/-- **Naturality of the relator value in the coefficients.** -/
theorem relVal_map (ρ : M →* M') {A B : Fin n → G} (hAB : commProd A B = 1)
    (f : TrivCocycle G M) : relVal A B ⟨_, TrivCocycle.map_mem ρ f.2⟩ = ρ (relVal A B f) := by
  set f' : TrivCocycle G M' := ⟨_, TrivCocycle.map_mem ρ f.2⟩
  let τ : Twist f →* Twist f' :=
    { toFun := fun x ↦ ⟨ρ x.m, x.g⟩
      map_one' := by
        ext
        · exact map_inv ρ _
        · rfl
      map_mul' := fun x y ↦ by
        ext
        · exact map_mul ρ _ _ |>.trans (by rw [map_mul]; rfl)
        · rfl }
  have hτ (c : M) : τ (Twist.incl c) = Twist.incl (ρ c) := by
    ext
    · change ρ (c * (f.1 (1, 1))⁻¹) = ρ c * (ρ (f.1 (1, 1)))⁻¹
      rw [map_mul, map_inv]
    · rfl
  apply Twist.incl_injective (f := f')
  rw [← hτ, ← commProd_eq_incl_relVal hAB f (fun i ↦ ⟨1, A i⟩) (fun i ↦ ⟨1, B i⟩)
    (fun _ ↦ rfl) (fun _ ↦ rfl), map_commProd]
  exact (commProd_eq_incl_relVal hAB f' (fun i ↦ τ ⟨1, A i⟩) (fun i ↦ τ ⟨1, B i⟩)
    (fun _ ↦ rfl) (fun _ ↦ rfl)).symm

/-- The coboundary `(g, h) ↦ x h / x (g h) * x g` (trivial action) of a 1-cochain `x`. -/
def dxTriv (x : G → M) : G × G → M := fun p ↦ x p.2 / x (p.1 * p.2) * x p.1

lemma dxTriv_mem (x : G → M) : dxTriv x ∈ TrivCocycle G M := fun a b c ↦ by
  simp only [dxTriv, mul_assoc]
  pi1_mul_abel

/-- **The relator value kills coboundaries.** -/
theorem relVal_dx {A B : Fin n → G} (hAB : commProd A B = 1) (x : G → M) :
    relVal A B ⟨dxTriv x, dxTriv_mem x⟩ = 1 := by
  set f : TrivCocycle G M := ⟨dxTriv x, dxTriv_mem x⟩
  let χ : Twist f →* M :=
    { toFun := fun y ↦ y.m * x y.g
      map_one' := by
        change (dxTriv x (1, 1))⁻¹ * x 1 = 1
        simp only [dxTriv, mul_one]
        pi1_mul_abel
      map_mul' := fun y z ↦ by
        change y.m * z.m * dxTriv x (y.g, z.g) * x (y.g * z.g) = y.m * x y.g * (z.m * x z.g)
        simp only [dxTriv]
        pi1_mul_abel }
  have hχ (c : M) : χ (Twist.incl c) = c := by
    change c * (dxTriv x (1, 1))⁻¹ * x 1 = c
    simp only [dxTriv, mul_one]
    pi1_mul_abel
  rw [← hχ (relVal A B f), ← commProd_eq_incl_relVal hAB f (fun i ↦ ⟨1, A i⟩)
    (fun i ↦ ⟨1, B i⟩) (fun _ ↦ rfl) (fun _ ↦ rfl), map_commProd]
  exact commProd_eq_one_of_comm _ _

/-- Over a commutative group, the commutator of two elements of `M ×_f V` is
`ι (f(x, y) / f(y, x))`. -/
lemma Twist.commutator_eq_incl {V : Type*} [CommGroup V] {f : TrivCocycle V M}
    (x y : Twist f) :
    x * y * x⁻¹ * y⁻¹ = Twist.incl (f.1 (x.g, y.g) / f.1 (y.g, x.g)) := by
  have hg : (x * y).g = (y * x).g := by simp [mul_comm]
  have h := Twist.eq_mul_incl hg
  have : x * y * x⁻¹ * y⁻¹ = (x * y) * (y * x)⁻¹ := by group
  rw [this, h, ← Twist.incl_mul_comm, mul_inv_rev, mul_inv_cancel_left, ← map_inv]
  congr 1
  simp only [Twist.mul_m]
  pi1_mul_abel

end RelVal

/-- Continuous homomorphisms to finite groups are their own extensions. -/
lemma liftFinite_comp_eta {G : Type u} [Group G] {P : Type u} [Group P] [Finite P]
    (φ : completion (GrpCat.of G) →* P) (hφ : ∀ p, IsOpen (φ ⁻¹' {p}))
    (z : completion (GrpCat.of G)) : liftFinite (φ.comp (eta (GrpCat.of G)).hom) z = φ z := by
  obtain ⟨x, hx, hx'⟩ := exists_etaFn_eq (φ.comp (eta (GrpCat.of G)).hom) (hφ (φ z)) rfl
  rw [← hx']
  exact hx

end Profinite

namespace SurfaceGroup

open Profinite

variable {g : ℕ}

/-- The generator `aᵢ` of `Π̂_{g,0}`. -/
noncomputable abbrev genAhat (i : Fin g) : ProfiniteSurfaceGroup g 0 :=
  etaFn (GrpCat.of (SurfaceGroup g 0)) (genA i)

/-- The generator `bᵢ` of `Π̂_{g,0}`. -/
noncomputable abbrev genBhat (i : Fin g) : ProfiniteSurfaceGroup g 0 :=
  etaFn (GrpCat.of (SurfaceGroup g 0)) (genB i)

/-- The surface relation `∏ᵢ [aᵢ, bᵢ] = 1` in `Π̂_{g,0}`. -/
theorem commProd_genAhat : commProd (genAhat (g := g)) genBhat = 1 := by
  have h := congrArg (eta (GrpCat.of (SurfaceGroup g 0))).hom (relation (g := g) (r := 0))
  rw [map_mul, map_commProd, map_ordProd, ordProd, List.ofFn_zero, List.prod_nil, mul_one,
    map_one] at h
  exact h

variable {M : Type} [CommGroup M]

/-- **A locally constant cocycle with trivial relator value is a coboundary.** -/
theorem exists_of_relVal_eq_one [Finite M] (f : TrivCocycle (ProfiniteSurfaceGroup g 0) M)
    (hf : IsLocallyConstant f.1) (h : relVal genAhat genBhat f = 1) :
    ∃ x : ProfiniteSurfaceGroup g 0 → M, IsLocallyConstant x ∧
      ∀ γ δ, f.1 (γ, δ) = x δ / x (γ * δ) * x γ := by
  obtain ⟨U, hUn, hUo, F, hF⟩ := TrivCocycle.exists_inflation f.2 hf
  haveI : Finite (ProfiniteSurfaceGroup g 0 ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hUo
  haveI := Twist.finite F
  let q : ProfiniteSurfaceGroup g 0 →* ProfiniteSurfaceGroup g 0 ⧸ U := QuotientGroup.mk' U
  have hfF : f = ⟨_, TrivCocycle.comap_mem q F.2⟩ := Subtype.ext (funext fun p ↦ (hF p.1 p.2).symm)
  have hF1 : relVal (fun i ↦ q (genAhat i)) (fun i ↦ q (genBhat i)) F = 1 := by
    rw [← relVal_comap q commProd_genAhat F, ← hfF, h]
  -- the splitting over the finite quotient
  have hrel : commProd (fun i ↦ (⟨1, q (genAhat i)⟩ : Twist F)) (fun i ↦ ⟨1, q (genBhat i)⟩) *
      ordProd (Fin.elim0 : Fin 0 → Twist F) = 1 := by
    rw [ordProd, List.ofFn_zero, List.prod_nil, mul_one,
      commProd_eq_incl_relVal (by rw [← map_commProd, commProd_genAhat, map_one]) F _ _
        (fun _ ↦ rfl) (fun _ ↦ rfl), hF1, map_one]
  let s₀ : SurfaceGroup g 0 →* Twist F := lift _ _ _ hrel
  let s : ProfiniteSurfaceGroup g 0 →* Twist F := liftFinite s₀
  have hs : ∀ e, IsOpen (s ⁻¹' {e}) := isOpen_liftFinite_fiber s₀
  have hsq (γ : ProfiniteSurfaceGroup g 0) : (s γ).g = q γ := by
    have h1 : Twist.proj.comp s₀ = q.comp (eta (GrpCat.of (SurfaceGroup g 0))).hom := by
      refine hom_ext (fun i ↦ ?_) (fun i ↦ ?_) (fun j ↦ j.elim0)
      · change Twist.proj (s₀ (genA i)) = q (genAhat i)
        simp [s₀]
      · change Twist.proj (s₀ (genB i)) = q (genBhat i)
        simp [s₀]
    have := liftFinite_comp s₀ Twist.proj γ
    rw [h1, liftFinite_comp_eta q (H2lc.isOpen_mk_fiber U hUo)] at this
    exact this.symm
  obtain ⟨x, hx, hxf⟩ := Twist.exists_of_section q s hs hsq
  refine ⟨x, hx, fun γ δ ↦ ?_⟩
  rw [← hxf, ← hF]
  rfl

/-- The bilinear map `(s, t) ↦ c ^ (s t)` on `ℤ/n`, for `c ^ n = 1`. -/
noncomputable def heisPair {n : ℕ} (c : M) (hc : c ^ n = 1) : ZMod n →+ Additive M :=
  ZMod.lift n ⟨zmultiplesHom (Additive M) (Additive.ofMul c), by
    simp only [zmultiplesHom_apply, natCast_zsmul]
    rw [← ofMul_pow, hc, ofMul_one]⟩

lemma heisPair_one {n : ℕ} (c : M) (hc : c ^ n = 1) : heisPair c hc 1 = Additive.ofMul c := by
  have := ZMod.lift_coe n ⟨zmultiplesHom (Additive M) (Additive.ofMul c), by
    simp only [zmultiplesHom_apply, natCast_zsmul]
    rw [← ofMul_pow, hc, ofMul_one]⟩ 1
  simpa [heisPair] using this

/-- The Heisenberg cocycle `((u, v), (u', v')) ↦ c ^ (u v')` on `(ℤ/n)²`. -/
noncomputable def heisCocycle {n : ℕ} (c : M) (hc : c ^ n = 1) :
    TrivCocycle (Multiplicative (ZMod n) × Multiplicative (ZMod n)) M :=
  ⟨fun p ↦ Additive.toMul (heisPair c hc (p.1.1.toAdd * p.2.2.toAdd)), fun a b d ↦ by
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, add_mul, mul_add, map_add, toMul_add]
    pi1_mul_abel⟩

/-- **Every element of `M` is a relator value** (of a Heisenberg cocycle), for `g ≥ 1`. -/
theorem exists_relVal_eq [Finite M] (hg : 0 < g) (c : M) :
    ∃ f : TrivCocycle (ProfiniteSurfaceGroup g 0) M, IsLocallyConstant f.1 ∧
      relVal genAhat genBhat f = c := by
  classical
  set n := Nat.card M
  haveI : NeZero n := ⟨Nat.card_pos.ne'⟩
  have hc : c ^ n = 1 := pow_card_eq_one'
  let i₀ : Fin g := ⟨0, hg⟩
  let e : Fin g → Multiplicative (ZMod n) := fun i ↦ if i = i₀ then Multiplicative.ofAdd 1 else 1
  let α₀ : SurfaceGroup g 0 →* Multiplicative (ZMod n) :=
    lift e (fun _ ↦ 1) Fin.elim0 (by
      rw [commProd_eq_one_of_comm, one_mul, ordProd, List.ofFn_zero, List.prod_nil])
  let β₀ : SurfaceGroup g 0 →* Multiplicative (ZMod n) :=
    lift (fun _ ↦ 1) e Fin.elim0 (by
      rw [commProd_eq_one_of_comm, one_mul, ordProd, List.ofFn_zero, List.prod_nil])
  let ab : ProfiniteSurfaceGroup g 0 →* Multiplicative (ZMod n) × Multiplicative (ZMod n) :=
    (liftFinite α₀).prod (liftFinite β₀)
  let H := heisCocycle c hc
  refine ⟨⟨_, TrivCocycle.comap_mem ab H.2⟩, ?_, ?_⟩
  · have hα : IsLocallyConstant (liftFinite α₀) :=
      IsLocallyConstant.iff_isOpen_fiber.2 (isOpen_liftFinite_fiber α₀)
    have hβ : IsLocallyConstant (liftFinite β₀) :=
      IsLocallyConstant.iff_isOpen_fiber.2 (isOpen_liftFinite_fiber β₀)
    exact IsLocallyConstant.comp₂ (hα.comp_continuous continuous_fst)
      (hβ.comp_continuous continuous_snd)
      (fun u v ↦ Additive.toMul (heisPair c hc (u.toAdd * v.toAdd)))
  · rw [relVal_comap ab commProd_genAhat H]
    apply Twist.incl_injective (f := H)
    rw [← commProd_eq_incl_relVal (by rw [← map_commProd, commProd_genAhat, map_one]) H
      (fun i ↦ ⟨1, ab (genAhat i)⟩) (fun i ↦ ⟨1, ab (genBhat i)⟩) (fun _ ↦ rfl) (fun _ ↦ rfl),
      commProd, prod_ofFn_eq_of_eq_one _ i₀, Twist.commutator_eq_incl]
    · congr 1
      simp [H, heisCocycle, ab, α₀, β₀, e, i₀, heisPair_one]
    · intro i hi
      rw [Twist.commutator_eq_incl, ← map_one (Twist.incl (f := H))]
      congr 1
      simp [H, heisCocycle, ab, α₀, β₀, e, hi]

/-! ### `H²(Π̂_{g,0}, M) ≅ M` -/

variable [MulDistribMulAction (ProfiniteSurfaceGroup g 0) M]

/-- The relator value on locally constant cocycles, for a trivial action. -/
noncomputable def h2Hom (htriv : ∀ (γ : ProfiniteSurfaceGroup g 0) (m : M), γ • m = m) :
    H2lc.cocycles (ProfiniteSurfaceGroup g 0) M →* M where
  toFun f := relVal genAhat genBhat ⟨f.1, mem_trivCocycle_of_mem_cocycles htriv f.2⟩
  map_one' := by
    have h := relVal_mul commProd_genAhat (1 : TrivCocycle (ProfiniteSurfaceGroup g 0) M) 1
    rw [mul_one] at h
    exact left_eq_mul.1 h |>.symm ▸ rfl
  map_mul' f₁ f₂ := relVal_mul commProd_genAhat
    ⟨f₁.1, mem_trivCocycle_of_mem_cocycles htriv f₁.2⟩
    ⟨f₂.1, mem_trivCocycle_of_mem_cocycles htriv f₂.2⟩

lemma coboundaries_le_ker_h2Hom (htriv : ∀ (γ : ProfiniteSurfaceGroup g 0) (m : M), γ • m = m) :
    H2lc.coboundaries (ProfiniteSurfaceGroup g 0) M ≤ (h2Hom htriv).ker := by
  rintro f ⟨x, -, hx⟩
  rw [MonoidHom.mem_ker]
  have : (⟨f.1, mem_trivCocycle_of_mem_cocycles htriv f.2⟩ :
      TrivCocycle (ProfiniteSurfaceGroup g 0) M) = ⟨dxTriv x, dxTriv_mem x⟩ := by
    refine Subtype.ext ?_
    rw [← hx]
    ext ⟨γ, δ⟩
    simp [H2lc.dx, dxTriv, htriv]
  change relVal _ _ _ = 1
  rw [this]
  exact relVal_dx commProd_genAhat x

/-- **`H²(Π̂_{g,0}, M) ≅ M`** for `g ≥ 1` and a finite commutative group `M` with trivial action
(locally constant cochains, i.e. continuous cohomology with discrete coefficients); the
isomorphism is the relator value: `∏ᵢ [âᵢ, b̂ᵢ] = ι(h2Equiv [f])` in the central extension
`1 → M → M ×_f Π̂_{g,0} → Π̂_{g,0} → 1` defined by `f`. -/
noncomputable def h2Equiv [Finite M] (hg : 0 < g)
    (htriv : ∀ (γ : ProfiniteSurfaceGroup g 0) (m : M), γ • m = m) :
    H2lc (ProfiniteSurfaceGroup g 0) M ≃* M :=
  MulEquiv.ofBijective (QuotientGroup.lift _ (h2Hom htriv) (coboundaries_le_ker_h2Hom htriv)) <| by
    constructor
    · rw [injective_iff_map_eq_one]
      intro a ha
      induction a using QuotientGroup.induction_on with | H f => ?_
      change (QuotientGroup.mk f : H2lc.cocycles _ M ⧸ H2lc.coboundaries _ M) = 1
      rw [QuotientGroup.eq_one_iff]
      obtain ⟨x, hx, hxf⟩ := exists_of_relVal_eq_one
        ⟨f.1, mem_trivCocycle_of_mem_cocycles htriv f.2⟩ f.2.1 ha
      refine ⟨x, hx, ?_⟩
      ext ⟨γ, δ⟩
      rw [hxf]
      simp [H2lc.dx, htriv]
    · intro c
      obtain ⟨f, hf, hfc⟩ := exists_relVal_eq hg c
      refine ⟨QuotientGroup.mk ⟨f.1, hf, fun a b d ↦ ?_⟩, hfc⟩
      rw [htriv]
      exact TrivCocycle.cond f.2 a b d

theorem h2Equiv_mk [Finite M] (hg : 0 < g)
    (htriv : ∀ (γ : ProfiniteSurfaceGroup g 0) (m : M), γ • m = m)
    (f : H2lc.cocycles (ProfiniteSurfaceGroup g 0) M) :
    h2Equiv hg htriv (QuotientGroup.mk f) =
      relVal genAhat genBhat ⟨f.1, mem_trivCocycle_of_mem_cocycles htriv f.2⟩ :=
  rfl

/-- **`H²(Π̂_{g,0}, M)` is nontrivial** for `g ≥ 1` and nontrivial finite `M` with trivial
action (whereas it vanishes for open subgroups of free profinite groups). -/
theorem nontrivial_h2 [Finite M] [Nontrivial M] (hg : 0 < g)
    (htriv : ∀ (γ : ProfiniteSurfaceGroup g 0) (m : M), γ • m = m) :
    Nontrivial (H2lc (ProfiniteSurfaceGroup g 0) M) :=
  (h2Equiv hg htriv).toEquiv.nontrivial

/-- The trivial action of a group on a commutative group. -/
abbrev trivialAction (G M : Type*) [Group G] [CommGroup M] : MulDistribMulAction G M where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

omit [MulDistribMulAction (ProfiniteSurfaceGroup g 0) M] in
/-- **`H²(G, M) ≅ M` for every topological group `G ≃ₜ* Π̂_{g,0}`** (`g ≥ 1`, `M` finite with
trivial action), e.g. the geometric fundamental group `Δ_X` of a proper curve of genus `g ≥ 1` in
characteristic `0`, with coefficients `μ_n`. -/
noncomputable def h2EquivOfContinuousMulEquiv {G : Type*} [Group G] [TopologicalSpace G]
    [Finite M] (hg : 0 < g) (e : G ≃ₜ* ProfiniteSurfaceGroup g 0) [MulDistribMulAction G M]
    (htriv : ∀ (γ : G) (m : M), γ • m = m) : H2lc G M ≃* M :=
  letI := trivialAction (ProfiniteSurfaceGroup g 0) M
  (H2lc.congr e fun γ m ↦ (htriv γ m).symm).trans (h2Equiv hg fun _ _ ↦ rfl)

end SurfaceGroup

end Pi1
