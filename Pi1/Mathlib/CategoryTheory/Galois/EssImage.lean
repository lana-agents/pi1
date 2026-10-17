/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.CategoryTheory.Galois.Equivalence
public import Pi1.Mathlib.CategoryTheory.Galois.FiberAutMap

/-!
# Objects in the essential image of a functor between Galois categories

Let `C`, `D` be Galois categories with fibre functors `F`, `G`, `H : D ⥤ C` and
`e : H ⋙ F ≅ G`, such that `φ = fiberAutMap e : Aut F →* Aut G` is surjective. If the kernel of
`φ` acts trivially on the fibre `F B` of an object `B` of `C`, then `B` is isomorphic to `H A` for
some `A : D` (`PreGaloisCategory.exists_iso_obj_of_forall_ker_smul_eq`): the action of `Aut F` on
`F B` descends to a continuous action of `Aut G` (`φ` is a quotient map, being a continuous
surjection between compact Hausdorff spaces), which is the fibre of some `A` by the equivalence
between `D` and finite continuous `Aut G`-sets (`PreGaloisCategory.functorToContAction`); the
fibres of `H A` and `B` are then isomorphic as `Aut F`-sets, hence `H A ≅ B`.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

open CategoryTheory Limits Functor

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] {D : Type v₁} [Category.{v₂} D]
  [GaloisCategory C] [GaloisCategory D] {F : C ⥤ FintypeCat.{w}} {G : D ⥤ FintypeCat.{w}}
  [FiberFunctor F] [FiberFunctor G] {H : D ⥤ C} (e : H ⋙ F ≅ G)

open scoped FintypeCatDiscrete

section Descent

variable (hφ : Function.Surjective (fiberAutMap e)) (B : C)
  (hB : ∀ σ : Aut F, fiberAutMap e σ = 1 → ∀ b : F.obj B, σ.hom.app B b = b)

omit [GaloisCategory C] [GaloisCategory D] [FiberFunctor F] [FiberFunctor G] in
include hB in
lemma app_eq_of_fiberAutMap_eq {σ τ : Aut F} (h : fiberAutMap e σ = fiberAutMap e τ)
    (b : F.obj B) : σ.hom.app B b = τ.hom.app B b := by
  have h1 : fiberAutMap e (τ⁻¹ * σ) = 1 := by rw [map_mul, h, _root_.map_inv, inv_mul_cancel]
  have h2 := hB _ h1 b
  rw [Aut.Aut_mul_def] at h2
  have h3 := congrArg (τ.hom.app B) h2
  simp only [Iso.trans_hom, NatTrans.comp_app, FintypeCat.comp_apply] at h3
  rw [← h3]
  change _ = τ.hom.app B ((τ.inv.app B) (σ.hom.app B b))
  exact (FintypeCat.inv_hom_id_apply (τ.app B) _).symm

omit [GaloisCategory C] [GaloisCategory D] [FiberFunctor F] [FiberFunctor G] in
/-- The descended action of `Aut G` on `F B`. -/
@[reducible] noncomputable def descendedMulAction : MulAction (Aut G) (F.obj B) where
  smul g b := (Function.surjInv hφ g).hom.app B b
  one_smul b := by
    change (Function.surjInv hφ 1).hom.app B b = b
    exact hB _ (Function.surjInv_eq hφ 1) b
  mul_smul g h b := by
    change (Function.surjInv hφ (g * h)).hom.app B b =
      (Function.surjInv hφ g).hom.app B ((Function.surjInv hφ h).hom.app B b)
    have : fiberAutMap e (Function.surjInv hφ (g * h)) =
        fiberAutMap e (Function.surjInv hφ g * Function.surjInv hφ h) := by
      rw [map_mul, Function.surjInv_eq hφ, Function.surjInv_eq hφ, Function.surjInv_eq hφ]
    rw [app_eq_of_fiberAutMap_eq e B hB this]
    rfl

omit [GaloisCategory C] [GaloisCategory D] [FiberFunctor F] [FiberFunctor G] in
lemma descended_smul_fiberAutMap (σ : Aut F) (b : F.obj B) :
    (descendedMulAction e hφ B hB).smul (fiberAutMap e σ) b = σ.hom.app B b :=
  app_eq_of_fiberAutMap_eq e B hB (Function.surjInv_eq hφ _) b

omit [GaloisCategory C] [GaloisCategory D] in
/-- The descended `Aut G`-set `F B` is continuous (`F B` discrete). -/
lemma continuous_descended_smul (b : F.obj B) :
    Continuous fun g : Aut G ↦ (descendedMulAction e hφ B hB).smul g b := by
  have hq : Topology.IsQuotientMap (fiberAutMap e) :=
    Topology.IsQuotientMap.of_surjective_continuous hφ (continuous_fiberAutMap e)
  rw [hq.continuous_iff]
  have : (fun g : Aut G ↦ (descendedMulAction e hφ B hB).smul g b) ∘ fiberAutMap e =
      fun σ : Aut F ↦ σ • b := by
    ext σ
    exact descended_smul_fiberAutMap e hφ B hB σ b
  rw [this]
  exact continuous_id.smul continuous_const

include e hφ hB in
/-- **Descent of objects.** If `fiberAutMap e : Aut F →* Aut G` is surjective and its kernel
acts trivially on `F B`, then `B ≅ H A` for some `A : D`. -/
theorem exists_iso_obj_of_forall_ker_smul_eq : ∃ A : D, Nonempty (H.obj A ≅ B) := by
  letI := descendedMulAction e hφ B hB
  let X : Action FintypeCat.{w} (Aut G) := Action.FintypeCat.ofMulAction (Aut G) (F.obj B)
  have hX : X.IsContinuous := by
    rw [Action.isContinuous_def]
    haveI : DiscreteTopology ((forget₂ (Action FintypeCat.{w} (Aut G)) TopCat).obj X) := ⟨rfl⟩
    refine continuous_prod_of_discrete_right.mpr fun b ↦ ?_
    exact continuous_descended_smul e hφ B hB b
  let A := (functorToContAction G).objPreimage ⟨X, hX⟩
  let i := (functorToContAction G).objObjPreimageIso ⟨X, hX⟩
  let i' : G.obj A ≅ F.obj B := (Action.forget _ _).mapIso ((ObjectProperty.ι _).mapIso i)
  have hi' (g : Aut G) (y : G.obj A) :
      i'.hom (g.hom.app A y) = (descendedMulAction e hφ B hB).smul g (i'.hom y) :=
    congr($((ObjectProperty.ι _).map i.hom |>.comm g) y)
  let j : (functorToContAction F).obj (H.obj A) ≅ (functorToContAction F).obj B :=
    ObjectProperty.isoMk _ (Action.mkIso (e.app A ≪≫ i') fun σ ↦ by
      ext x
      change i'.hom (e.hom.app A (σ.hom.app (H.obj A) x)) = σ.hom.app B (i'.hom (e.hom.app A x))
      have h1 : e.hom.app A (σ.hom.app (H.obj A) x) =
          (fiberAutMap e σ).hom.app A (e.hom.app A x) := by
        rw [fiberAutMap_hom_app_apply]
        congr 2
        exact (FintypeCat.hom_inv_id_apply (e.app A) x).symm
      rw [h1, hi', descended_smul_fiberAutMap])
  exact ⟨A, ⟨(functorToContAction F).preimageIso j⟩⟩

end Descent

section Quotient

variable (F)

include F in
/-- **Every open subgroup is a stabilizer.** For an open subgroup `V` of `Aut F` there are an
object `A` and a point `a ∈ F A` whose stabilizer is `V` (the object with fibre `Aut F ⧸ V`;
this version works for fibre functors to `FintypeCat` in any universe). -/
theorem exists_obj_stabilizer_eq (V : Subgroup (Aut F)) (hV : IsOpen (V : Set (Aut F))) :
    ∃ (A : C) (a : F.obj A), ∀ σ : Aut F, σ.hom.app A a = a ↔ σ ∈ V := by
  have : Finite (Aut F ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  have : DiscreteTopology (Aut F ⧸ V) := QuotientGroup.discreteTopology hV
  let n := Nat.card (Aut F ⧸ V)
  let eq : Aut F ⧸ V ≃ ULift.{w} (Fin n) := (Finite.equivFin _).trans Equiv.ulift.symm
  letI : MulAction (Aut F) (ULift.{w} (Fin n)) := eq.symm.mulAction (Aut F)
  have hsmul (σ : Aut F) (x : ULift.{w} (Fin n)) : σ • x = eq (σ • eq.symm x) := rfl
  let X : Action FintypeCat.{w} (Aut F) :=
    Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of (ULift.{w} (Fin n)))
  have hX : X.IsContinuous := by
    rw [Action.isContinuous_def]
    haveI : DiscreteTopology ((forget₂ (Action FintypeCat.{w} (Aut F)) TopCat).obj X) := ⟨rfl⟩
    refine continuous_prod_of_discrete_right.mpr fun x ↦ ?_
    let g : Aut F → Aut F ⧸ V := fun σ ↦ σ • eq.symm x
    have hg : Continuous g := by
      obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (eq.symm x)
      have : g = fun σ ↦ ((σ * h : Aut F) : Aut F ⧸ V) := by
        ext σ
        simp only [g, ← hh]
        rfl
      rw [this]
      exact continuous_quotient_mk'.comp (continuous_id.mul continuous_const)
    haveI : DiscreteTopology ((forget₂ FintypeCat TopCat).obj X.V) := ⟨rfl⟩
    refine continuous_discrete_rng.mpr fun y ↦ ?_
    exact (isOpen_discrete (eq ⁻¹' (show Set (ULift.{w} (Fin n)) from {y}))).preimage hg
  let A := (functorToContAction F).objPreimage ⟨X, hX⟩
  let i := (functorToContAction F).objObjPreimageIso ⟨X, hX⟩
  let i' : F.obj A ≅ FintypeCat.of (ULift.{w} (Fin n)) :=
    (Action.forget _ _).mapIso ((ObjectProperty.ι _).mapIso i)
  have hi' (σ : Aut F) (y : F.obj A) : i'.hom (σ.hom.app A y) = σ • i'.hom y :=
    congr($((ObjectProperty.ι _).map i.hom |>.comm σ) y)
  refine ⟨A, i'.inv (eq (QuotientGroup.mk 1)), fun σ ↦ ?_⟩
  set a := i'.inv (eq (QuotientGroup.mk 1))
  have key : σ.hom.app A a = a ↔ i'.hom (σ.hom.app A a) = i'.hom a := by
    refine ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩
    have := congrArg i'.inv h
    rwa [FintypeCat.hom_inv_id_apply, FintypeCat.hom_inv_id_apply] at this
  rw [key, hi', hsmul]
  have hz : i'.hom (i'.inv (eq (QuotientGroup.mk 1))) = eq (QuotientGroup.mk 1) :=
    FintypeCat.inv_hom_id_apply i' _
  simp only [a]
  rw [hz, Equiv.symm_apply_apply, eq.injective.eq_iff]
  change (QuotientGroup.mk (σ * 1) : Aut F ⧸ V) = QuotientGroup.mk 1 ↔ _
  rw [mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]

end Quotient

end CategoryTheory.PreGaloisCategory
