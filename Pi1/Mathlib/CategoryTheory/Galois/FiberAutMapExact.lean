/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import Pi1.Mathlib.CategoryTheory.Galois.FiberAutMap

/-!
# A criterion for the image of `Aut F' → Aut F`

Let `C`, `C'` be Galois categories with fibre functors `F`, `F'`, `H : C ⥤ C'` and
`e : H ⋙ F' ≅ F`. We give a criterion for `γ : Aut F` to lie in the image of
`fiberAutMap e : Aut F' →* Aut F` (`PreGaloisCategory.mem_range_fiberAutMap`): it suffices that
`γ` fixes every point of `F (Y)` coming from a section `⊤ ⟶ H Y` in `C'`.

This is the group-theoretic part of the exactness in the middle of
`π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X) → π₁ᵉᵗ(Spec k)` (SGA 1 V.6.11, IX.6.1, Stacks 0BN6):

* a point of `F' (Y')` fixed by `Aut F'` comes from a section `⊤ ⟶ Y'`
  (`exists_hom_terminal_of_forall_smul_eq`);
* the image of `fiberAutMap e` is closed, and its closure is detected on Galois objects `A`:
  for `a ∈ F A`, the set of `σ` with `σ a` in the orbit of `a` under the image is a subgroup, and
  the quotient of `A` by the corresponding subgroup of `Aut A` turns orbits into fixed points.
-/

@[expose] public section

universe u₁ u₂ u₃

namespace CategoryTheory.PreGaloisCategory

open Limits Functor

section Section

variable {C' : Type u₁} [Category.{u₂} C'] [GaloisCategory C'] (F' : C' ⥤ FintypeCat.{u₂})
  [FiberFunctor F']

lemma subsingleton_fiber_terminal : Subsingleton (F'.obj (⊤_ C')) := by
  have h : IsTerminal (F'.obj (⊤_ C')) := IsTerminal.isTerminalObj F' _ terminalIsTerminal
  refine ⟨fun p q ↦ ?_⟩
  let P : FintypeCat.{u₂} := FintypeCat.of PUnit
  have := h.hom_ext (FintypeCat.homMk (X := P) fun _ ↦ p) (FintypeCat.homMk (X := P) fun _ ↦ q)
  exact congr($this (PUnit.unit : P))

/-- A point of `F' Y` fixed by `Aut F'` comes from a section `⊤ ⟶ Y`. -/
lemma exists_hom_terminal_of_forall_smul_eq {Y : C'} (y : F'.obj Y)
    (hy : ∀ σ : Aut F', σ.hom.app Y y = y) :
    ∃ s : ⊤_ C' ⟶ Y, ∀ p, F'.map s p = y := by
  obtain ⟨Z, i, z, hz, hZ, hi⟩ := fiber_in_connected_component F' Y y
  have hinj : Function.Injective (F'.map i) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback (F'.map i)).mp inferInstance
  have hsub (z' : F'.obj Z) : z' = z := by
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F') z z'
    apply hinj
    rw [← hσ, hz]
    change F'.map i (σ.hom.app Z z) = y
    rw [← FintypeCat.comp_apply, ← σ.hom.naturality, FintypeCat.comp_apply, hz, hy]
  haveI := subsingleton_fiber_terminal F'
  have hbij : Function.Bijective (F'.map (terminal.from Z)) :=
    ⟨fun a b _ ↦ (hsub a).trans (hsub b).symm,
      fun p ↦ ⟨z, Subsingleton.elim _ _⟩⟩
  haveI : IsIso (F'.map (terminal.from Z)) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI : IsIso (terminal.from Z) := isIso_of_reflects_iso _ F'
  refine ⟨inv (terminal.from Z) ≫ i, fun p ↦ ?_⟩
  rw [F'.map_comp, FintypeCat.comp_apply, hsub (F'.map _ p), hz]

end Section

section Quotient

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{u₂})
  [FiberFunctor F]

/-- Two points of `F A` with the same image in the quotient `A / G` (by a finite group `G`
acting on `A`) lie in the same `G`-orbit. -/
lemma exists_map_eq_of_map_colimit_ι_eq {G : Type u₂} [Group G] [Finite G] {A : C}
    (φ : G →* End A) {x x' : F.obj A}
    (h : F.map (colimit.ι (SingleObj.functor φ) (SingleObj.star G)) x =
      F.map (colimit.ι (SingleObj.functor φ) (SingleObj.star G)) x') :
    ∃ g : G, F.map (φ g) x' = x := by
  let E := preservesColimitIso (F ⋙ FintypeCat.incl) (SingleObj.functor φ)
  have hE (y : F.obj A) :
      E.hom ((F ⋙ FintypeCat.incl).map (colimit.ι (SingleObj.functor φ) (SingleObj.star G)) y) =
        colimit.ι (SingleObj.functor φ ⋙ F ⋙ FintypeCat.incl) (SingleObj.star G) y :=
    congr($(ι_preservesColimitIso_hom (F ⋙ FintypeCat.incl) (SingleObj.functor φ)
      (SingleObj.star G)) y)
  have h' := congr_arg (fun y ↦ SingleObj.Types.colimitEquivQuotient
    (SingleObj.functor φ ⋙ F ⋙ FintypeCat.incl) (E.hom y)) h
  change SingleObj.Types.colimitEquivQuotient _ (E.hom ((F ⋙ FintypeCat.incl).map _ x)) =
    SingleObj.Types.colimitEquivQuotient _ (E.hom ((F ⋙ FintypeCat.incl).map _ x')) at h'
  erw [hE, hE] at h'
  simp only [SingleObj.Types.colimitEquivQuotient, Equiv.trans_apply,
    Types.colimitEquivColimitType_apply] at h'
  obtain ⟨g, hg⟩ := Quotient.exact h'
  exact ⟨g, hg⟩

end Quotient

section Exact

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] {F : C ⥤ FintypeCat.{u₂}}
  [FiberFunctor F] {C' : Type u₃} [Category.{u₂} C'] [GaloisCategory C']
  {F' : C' ⥤ FintypeCat.{u₂}} [FiberFunctor F'] {H : C ⥤ C'}

omit [GaloisCategory C] [FiberFunctor F] [GaloisCategory C'] [FiberFunctor F'] in
/-- If `fiberAutMap e σ = 1`, then `σ` acts trivially on the fibres of objects in the image
of `H`. -/
lemma fiberAutMap_eq_one_apply (e : H ⋙ F' ≅ F) {σ : Aut F'} (h : fiberAutMap e σ = 1) (Y : C)
    (x : F'.obj (H.obj Y)) : σ.hom.app (H.obj Y) x = x := by
  have hei (w : F'.obj (H.obj Y)) : e.inv.app Y (e.hom.app Y w) = w :=
    FintypeCat.hom_inv_id_apply (e.app Y) w
  have h1 := congr_arg (fun τ : Aut F ↦ e.inv.app Y (τ.hom.app Y (e.hom.app Y x))) h
  simp only [fiberAutMap_hom_app_apply, hei] at h1
  rw [h1]
  exact hei x

/-- **Image criterion** (group-theoretic half of SGA 1 V.6.11): if `γ : Aut F` fixes every point
of `F Y` that comes from a section `⊤ ⟶ H Y` in `C'`, then `γ` lies in the image of
`fiberAutMap e : Aut F' →* Aut F`. -/
theorem mem_range_fiberAutMap (e : H ⋙ F' ≅ F) (γ : Aut F)
    (hγ : ∀ (Y : C) (s : ⊤_ C' ⟶ H.obj Y) (p : F'.obj (⊤_ C')),
      γ.hom.app Y (e.hom.app Y (F'.map s p)) = e.hom.app Y (F'.map s p)) :
    γ ∈ (fiberAutMap e).range := by
  have hei (Y : C) (w : F'.obj (H.obj Y)) : e.inv.app Y (e.hom.app Y w) = w :=
    FintypeCat.hom_inv_id_apply (e.app Y) w
  have hie (Y : C) (y : F.obj Y) : e.hom.app Y (e.inv.app Y y) = y :=
    FintypeCat.inv_hom_id_apply (e.app Y) y
  -- Step 1: `γ` fixes the points fixed by the image.
  have step1 (Y : C) (y : F.obj Y) (hy : ∀ δ : Aut F', (fiberAutMap e δ).hom.app Y y = y) :
      γ.hom.app Y y = y := by
    have hy' (σ : Aut F') : σ.hom.app (H.obj Y) (e.inv.app Y y) = e.inv.app Y y := by
      have := congr_arg (e.inv.app Y) (hy σ)
      rwa [fiberAutMap_hom_app_apply, hei] at this
    obtain ⟨s, hs⟩ := exists_hom_terminal_of_forall_smul_eq F' _ hy'
    have := hγ Y s (F'.map (terminal.from _) (e.inv.app Y y))
    rwa [hs, hie] at this
  -- Step 2: the image is closed.
  have hcl : IsClosed (Set.range (fiberAutMap e)) :=
    (isCompact_range (continuous_fiberAutMap e)).isClosed
  rw [← SetLike.mem_coe, MonoidHom.coe_range, ← hcl.closure_eq]
  -- Step 3: approximation on Galois objects.
  have hb := (nhds_one_has_basis_stabilizers F).map (γ * ·)
  rw [map_mul_left_nhds_one] at hb
  rw [mem_closure_iff_nhds_basis hb]
  rintro ⟨A, a, hA⟩ -
  -- the subgroup of `Aut A` moving `a` within its orbit under the image
  let K : Subgroup (Aut A) :=
    { carrier := {g | ∃ δ : Aut F', F.map g.hom a = (fiberAutMap e δ).hom.app A a}
      one_mem' := ⟨1, by
        rw [map_one]
        change F.map (𝟙 A) a = a
        rw [F.map_id, FintypeCat.id_apply]⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨δ₁, h₁⟩ ⟨δ₂, h₂⟩
        refine ⟨δ₂ * δ₁, ?_⟩
        rw [map_mul]
        change F.map (g₂.hom ≫ g₁.hom) a =
          (fiberAutMap e δ₂).hom.app A ((fiberAutMap e δ₁).hom.app A a)
        rw [F.map_comp, FintypeCat.comp_apply, h₂, ← FintypeCat.comp_apply,
          ← (fiberAutMap e δ₂).hom.naturality, FintypeCat.comp_apply, h₁]
      inv_mem' := by
        rintro g ⟨δ, hδ⟩
        obtain ⟨g', hg'⟩ := MulAction.exists_smul_eq (Aut A) a
          ((fiberAutMap e δ⁻¹).hom.app A a)
        refine ⟨δ⁻¹, ?_⟩
        change F.map g'.hom a = _ at hg'
        have hgg : g * g' = 1 := by
          apply evaluation_aut_injective_of_isConnected F A a
          change F.map (g'.hom ≫ g.hom) a = F.map (𝟙 A) a
          rw [F.map_comp, FintypeCat.comp_apply, hg', ← FintypeCat.comp_apply,
            ← (fiberAutMap e δ⁻¹).hom.naturality, FintypeCat.comp_apply, hδ, F.map_id,
            FintypeCat.id_apply, ← FintypeCat.comp_apply]
          change ((fiberAutMap e δ⁻¹) * fiberAutMap e δ).hom.app A a = a
          rw [← map_mul, inv_mul_cancel, map_one]
          rfl
        rw [inv_eq_of_mul_eq_one_right hgg]
        exact hg' }
  let φ : K →* End A := (Aut.toEnd A).comp K.subtype
  let q := colimit.ι (SingleObj.functor φ) (SingleObj.star K)
  have hq (g : K) : (g : Aut A).hom ≫ q = q :=
    colimit.w (SingleObj.functor φ) (g : SingleObj.star K ⟶ SingleObj.star K)
  -- the image fixes the image of `a` in the quotient `A / K`
  have hfix (δ : Aut F') : (fiberAutMap e δ).hom.app _ (F.map q a) = F.map q a := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut A) a ((fiberAutMap e δ).hom.app A a)
    change F.map g.hom a = _ at hg
    have h1 : (fiberAutMap e δ).hom.app _ (F.map q a) =
        F.map q ((fiberAutMap e δ).hom.app A a) := by
      rw [← FintypeCat.comp_apply, (fiberAutMap e δ).hom.naturality]
      rfl
    have h2 : F.map q (F.map g.hom a) = F.map (g.hom ≫ q) a := by
      rw [F.map_comp]
      rfl
    rw [h1, ← hg, h2, hq ⟨g, δ, hg⟩]
    rfl
  have hγq := step1 _ _ hfix
  rw [← FintypeCat.comp_apply, γ.hom.naturality, FintypeCat.comp_apply] at hγq
  obtain ⟨⟨g, δ, hδ⟩, hg⟩ := exists_map_eq_of_map_colimit_ι_eq F φ hγq
  change F.map g.hom a = γ.hom.app A a at hg
  have hγa : γ.hom.app A a = (fiberAutMap e δ).hom.app A a := hg.symm.trans hδ
  refine ⟨fiberAutMap e δ, ⟨δ, rfl⟩, γ⁻¹ * fiberAutMap e δ, ?_, by simp⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  change γ.inv.app A ((fiberAutMap e δ).hom.app A a) = a
  rw [← hγa]
  exact FintypeCat.hom_inv_id_apply (γ.app A) a

end Exact

end CategoryTheory.PreGaloisCategory
