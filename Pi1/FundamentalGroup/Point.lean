/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Pi1.FundamentalGroup.Galois
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# The étale fundamental group of a point

Let `k` be a field and `K` a separable closure of `k`. We show that the absolute Galois group
`Gal(K/k)` is a fundamental group for the fiber functor of `FiniteEtale (Spec k)` at the
geometric point `Spec K ⟶ Spec k` (`AlgebraicGeometry.FiniteEtale.isFundamentalGroup`).
In particular, `π₁ᵉᵗ(Spec k)` is isomorphic to `Gal(K/k)` as a topological group
(`AlgebraicGeometry.FiniteEtale.mulEquivAutFiber`).

Along the way we show that for a separably closed field `Ω` and a geometric point
`ξ : Spec Ω ⟶ S`, the fiber functor at `ξ` is isomorphic to `X ↦ Hom_S(Spec Ω, X)`
(`AlgebraicGeometry.FiniteEtale.fiberIsoCoyoneda`).
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

section

@[simp]
lemma CategoryTheory.Iso.commRingCatIsoToRingEquiv_symm {R S : CommRingCat}
    (e : R ≅ S) :
    e.symm.commRingCatIsoToRingEquiv = e.commRingCatIsoToRingEquiv.symm :=
  rfl

@[simp]
lemma CategoryTheory.Iso.ofHom_commRingCatIsoToRingEquiv {R S : CommRingCat}
    (e : R ≅ S) :
    CommRingCat.ofHom e.commRingCatIsoToRingEquiv = e.hom :=
  rfl

@[simp]
lemma CategoryTheory.Iso.ofHom_commRingCatIsoToRingEquiv_symm {R S : CommRingCat}
    (e : R ≅ S) :
    CommRingCat.ofHom e.commRingCatIsoToRingEquiv.symm = e.inv :=
  rfl

end

@[simp]
lemma IntermediateField.map_top {F E E' : Type*} [Field F] [Field E] [Field E'] [Algebra F E]
    [Algebra F E'] (f : E →ₐ[F] E') :
    map f (⊤ : IntermediateField F E) = f.fieldRange := by
  ext : 1
  simp only [map, top_toSubalgebra, Algebra.map_top, AlgHom.mem_fieldRange]
  rfl

lemma IntermediateField.FG.finite_of_isAlgebraic {F E : Type*}
    [Field F] [Field E] [Algebra F E]
    {L : IntermediateField F E} (hL : L.FG)
    [Algebra.IsAlgebraic F E] :
    Module.Finite F L := by
  have : Algebra.EssFiniteType F ↥L := by
    rwa [IntermediateField.essFiniteType_iff]
  apply Algebra.finite_of_essFiniteType_of_isAlgebraic

section

variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C]

@[simp]
lemma AlgEquiv.toRingHom_refl :
    (AlgEquiv.refl (R := R) (A₁ := A) : A →+* A) = RingHom.id _ :=
  rfl

end

section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

instance (A : Type*) [Semiring A] [Algebra k A] : MulAction (K ≃ₐ[k] K) (A →ₐ[k] K) where
  smul g x := (g : _ →ₐ[k] _).comp x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

lemma AlgEquiv.smul_algHom_def (A : Type*) [Semiring A] [Algebra k A]
    (g : K ≃ₐ[k] K) (x : A →ₐ[k] K) :
    g • x = (g : _ →ₐ[k] _).comp x :=
  rfl

/-- If `K/k` is normal, the automorphism group of `K/k` acts transitively on the
`k`-embeddings of a field `L` into `K`. -/
instance (L : Type*) [Field L] [Algebra k L] [Normal k K] :
    MulAction.IsPretransitive (K ≃ₐ[k] K) (L →ₐ[k] K) := by
  constructor
  intro x y
  letI : Algebra L K := x.toRingHom.toAlgebra
  haveI : IsScalarTower k L K := .of_algebraMap_eq fun a ↦ (x.commutes a).symm
  use AlgEquiv.ofBijective (y.liftNormal K) (AlgHom.normal_bijective k K K _)
  ext a
  exact y.liftNormal_commutes K a

end

namespace AlgebraicGeometry

namespace FiniteEtale

instance (X : Scheme.{u}) : IsFiniteEtale (𝟙 X) :=
  MorphismProperty.id_mem @IsFiniteEtale X

section Fiber

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ S)

/-- Morphisms `Spec Ω ⟶ X` over `S` correspond to sections of the base change of `X` along
`ξ : Spec Ω ⟶ S`. -/
noncomputable
def homEquivHomPullback (X : FiniteEtale S) :
    (Over.mk ξ ⟶ X.toComma) ≃ (mk (𝟙 (Spec (.of Ω))) ⟶ (pullback ξ).obj X) where
  toFun x := MorphismProperty.Over.homMk (Limits.pullback.lift x.left (𝟙 _) (by simp)) (by simp)
  invFun f := Over.homMk (f.left ≫ Limits.pullback.fst _ _) <| by
    have : f.left ≫ Limits.pullback.snd X.hom ξ = 𝟙 _ := Over.w f.hom
    simp [Limits.pullback.condition, reassoc_of% this]
  left_inv x := by ext; simp
  right_inv f := by
    apply MorphismProperty.Over.Hom.ext
    apply Limits.pullback.hom_ext
    · simp
    · exact (Limits.pullback.lift_snd _ _ _).trans (Over.w f.hom).symm

variable (Ω) in
/-- If `Ω` is separably closed, sections of a finite étale `Spec Ω`-scheme `P` correspond
to points of `P`. -/
noncomputable
def homEquivPoints [IsSepClosed Ω] (P : FiniteEtale (Spec (.of Ω))) :
    (mk (𝟙 (Spec (.of Ω))) ⟶ P) ≃ P.left :=
  Equiv.ofBijective (fun f ↦ f.left (default : Spec (.of Ω))) <| by
    constructor
    · intro f g hfg
      apply (forgetScheme Ω).map_injective
      ext x
      obtain rfl : x = (default : Spec (.of Ω)) := Subsingleton.elim (α := Spec (.of Ω)) _ _
      exact hfg
    · intro p
      obtain ⟨f, hf⟩ := (forgetScheme Ω).map_surjective
        (FintypeCat.homMk (fun _ ↦ p) :
          (forgetScheme Ω).obj (mk (𝟙 _)) ⟶ (forgetScheme Ω).obj P)
      exact ⟨f, congr($hf (default : Spec (.of Ω)))⟩

variable [IsSepClosed Ω]

/-- If `Ω` is separably closed, the fiber of `X` over the geometric point `ξ` is in bijection
with the `S`-morphisms `Spec Ω ⟶ X`. -/
noncomputable
def fiberObjEquivHom (X : FiniteEtale S) : (fiber ξ).obj X ≃ (Over.mk ξ ⟶ X.toComma) :=
  ((homEquivHomPullback ξ X).trans (homEquivPoints Ω _)).symm

lemma fiberObjEquivHom_symm_apply (X : FiniteEtale S) (x : Over.mk ξ ⟶ X.toComma) :
    (fiberObjEquivHom ξ X).symm x =
      Limits.pullback.lift x.left (𝟙 _) (by simp) (default : Spec (.of Ω)) :=
  rfl

@[simp]
lemma fiberObjEquivHom_symm_naturality {X Y : FiniteEtale S} (f : X ⟶ Y) (x) :
    (fiber ξ).map f ((fiberObjEquivHom ξ X).symm x) = (fiberObjEquivHom ξ Y).symm (x ≫ f.hom) := by
  rw [fiberObjEquivHom_symm_apply, fiberObjEquivHom_symm_apply]
  change ((pullback ξ).map f).left _ = _
  have : Limits.pullback.lift x.left (𝟙 _) (by simp) ≫ ((pullback ξ).map f).left =
      Limits.pullback.lift (x ≫ f.hom).left (𝟙 _) (by simp) := by
    apply Limits.pullback.hom_ext <;> simp
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans congr($this _)

@[reassoc]
lemma fiberObjEquivHom_naturality {X Y : FiniteEtale S} (f : X ⟶ Y) (x) :
    (fiberObjEquivHom ξ X x) ≫ f.hom = fiberObjEquivHom ξ Y ((fiber ξ).map f x) := by
  rw [← Equiv.symm_apply_eq, ← fiberObjEquivHom_symm_naturality, Equiv.symm_apply_apply]

/-- If `Ω` is separably closed, the fiber functor at `ξ` is isomorphic to the functor
`X ↦ Hom(Spec Ω, X)`. -/
noncomputable
def fiberIsoCoyoneda :
    fiber ξ ⋙ CategoryTheory.forget FintypeCat ≅ forget _ ⋙ coyoneda.obj ⟨Over.mk ξ⟩ :=
  NatIso.ofComponents (fun X ↦ (equivEquivIso (fiberObjEquivHom ξ X))) fun f ↦ by
    ext x
    exact (fiberObjEquivHom_naturality ξ f x).symm

end Fiber

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ S)

unif_hint (X : FiniteEtale S) where
  ⊢ (forget S ⋙ coyoneda.obj ⟨Over.mk ξ⟩).obj X ≟ (Over.mk ξ ⟶ X.toComma)

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

scoped notation3:arg "fib " k:arg K:arg =>
  FiniteEtale.fiber (Spec.map (CommRingCat.ofHom <| algebraMap k K))

scoped notation3:arg "ξ " k:arg K:arg => Spec.map (CommRingCat.ofHom <| algebraMap k K)

noncomputable
instance (X : FiniteEtale (Spec (.of k))) :
    SMul (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) where
  smul g x := Over.homMk (V := Over.mk (ξ k K)) (Spec.map (CommRingCat.ofHom (g : K →+* K)))
    (by
      dsimp only [Over.mk_left, Functor.const_obj_obj, Over.mk_hom]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AlgEquiv.toAlgHom_toRingHom,
      AlgHom.comp_algebraMap]) ≫ x

@[simp]
lemma algEquiv_smul_hom {X : FiniteEtale (Spec (.of k))} (g : K ≃ₐ[k] K)
    (x : Over.mk (ξ k K) ⟶ X.toComma) :
    (g • x).left = Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫ x.left :=
  rfl

variable (X : FiniteEtale (Spec (.of k)))

noncomputable
instance : MulAction (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) where
  smul g x := Over.homMk (V := Over.mk (ξ k K)) (Spec.map (CommRingCat.ofHom (g : K →+* K)))
    (by
      dsimp only [Over.mk_left, Functor.const_obj_obj, Over.mk_hom]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AlgEquiv.toAlgHom_toRingHom,
      AlgHom.comp_algebraMap]) ≫ x
  one_smul x := by ext1; simp [AlgEquiv.aut_one]
  mul_smul g h x := by ext1; simp [AlgEquiv.aut_mul]

/-- `Spec K`-valued points of `X` correspond to `k`-algebra maps `Γ(X, ⊤) ⟶ K`. -/
noncomputable
def homEquivAlgHom (X : FiniteEtale (Spec (.of k))) :
    (Over.mk (ξ k K) ⟶ X.toComma) ≃ (Γ(X.left, ⊤) →ₐ[k] K) where
  toFun x :=
    { __ := RingHom.comp (Scheme.ΓSpecIso _).hom.hom x.left.appTop.hom,
      commutes' a := by
        have := congr((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of K)).hom)
          ($(Over.w x).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm a)))
        dsimp only [Functor.const_obj_obj, Over.mk_left, Scheme.Hom.comp_app,
          TopologicalSpace.Opens.map_top, CommRingCat.hom_comp, RingHom.coe_comp,
          Function.comp_apply, Functor.id_obj, Over.mk_hom] at this
        dsimp only [Over.mk_left, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
          MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply]
        rw [RingHom.algebraMap_toAlgebra]
        dsimp [Scheme.Hom.appTop]
        convert this
        · simp [Scheme.Hom.appLE]
        · dsimp [Iso.commRingCatIsoToRingEquiv]
          rw [← ConcreteCategory.comp_apply]
          simp [RingHom.comp_apply, Scheme.ΓSpecIso_naturality]
        }
  invFun x := Over.homMk
      (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ X.left.isoSpec.inv) <| by
    have := x.comp_algebraMap
    dsimp
    rw [← this]
    simp only [Category.assoc, CommRingCat.ofHom_comp, Spec.map_comp]
    congr
    rw [RingHom.algebraMap_toAlgebra]
    dsimp only [OverClass.fromOver_over, RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp,
      CommRingCat.ofHom_hom]
    rw [Spec.map_comp, Scheme.Hom.appLE]
    simp only [TopologicalSpace.Opens.map_top, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv]
    rfl
  left_inv x := by
    ext1
    dsimp
    rw [Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp_assoc, Iso.inv_hom_id]
    simp
  right_inv x := by
    apply AlgHom.coe_ringHom_injective
    dsimp
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    simp only [Category.assoc, Scheme.ΓSpecIso_naturality]
    rw [← Scheme.Hom.appTop]
    change CommRingCat.Hom.hom (X.left.isoSpec.inv.appTop ≫
        (Scheme.ΓSpecIso Γ(X.left, ⊤)).hom ≫ CommRingCat.ofHom x.toRingHom) = _
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop_assoc,
      Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop, Category.id_comp]
    simp

lemma homEquivAlgHom_smul (X : FiniteEtale (Spec (.of k))) (g : K ≃ₐ[k] K) (x) :
    (homEquivAlgHom k K X) (g • x) = g • (homEquivAlgHom k K X x) := by
  rw [homEquivAlgHom]
  dsimp only [Over.mk_left, AlgHom.toRingHom_eq_coe, Equiv.coe_fn_mk, algEquiv_smul_hom,
    Scheme.Hom.comp_app, TopologicalSpace.Opens.map_top, CommRingCat.hom_comp]
  rw [AlgEquiv.smul_algHom_def]
  ext1 a
  dsimp only [AlgHom.coe_mk, RingHom.coe_comp, Function.comp_apply, AlgHom.coe_comp, AlgHom.coe_coe]
  rw [← ConcreteCategory.comp_apply]
  simp

lemma homEquivAlgHom_comp {X Y : FiniteEtale (Spec (.of k))} (f : X ⟶ Y)
    (x : Over.mk (ξ k K) ⟶ X.toComma) (a : Γ(Y.left, ⊤)) :
    homEquivAlgHom k K Y (x ≫ f.hom) a = homEquivAlgHom k K X x (f.left.appTop a) := by
  simp [homEquivAlgHom]

scoped instance : TopologicalSpace (Over.mk (ξ k K) ⟶ X.toComma) := ⊥

instance : DiscreteTopology (Over.mk (ξ k K) ⟶ X.toComma) := ⟨rfl⟩

instance : ContinuousSMul (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  let φ := homEquivAlgHom k K X x
  let b := Module.Free.chooseBasis k Γ(X.left, ⊤)
  let E : IntermediateField k K := IntermediateField.adjoin k (Set.range (φ ∘ b))
  have : FiniteDimensional k E := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro - ⟨i, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (b i)).map φ
  refine Subgroup.isOpen_mono (fun g hg ↦ ?_) (IntermediateField.fixingSubgroup_isOpen E)
  rw [MulAction.mem_stabilizer_iff]
  apply (homEquivAlgHom k K X).injective
  rw [homEquivAlgHom_smul]
  apply AlgHom.toLinearMap_injective
  apply b.ext
  intro i
  exact (IntermediateField.mem_fixingSubgroup_iff E g).mp hg _
    (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

/-- If `X` is connected, the underlying scheme of `X` has exactly one point. -/
lemma nonempty_and_subsingleton_of_isConnected [IsConnected X] :
    Nonempty X.left ∧ Subsingleton X.left := by
  let Ω : Type u := AlgebraicClosure k
  let F := fib k Ω
  refine ⟨?_, ?_⟩
  · obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
    exact ⟨Limits.pullback.fst X.hom _ x⟩
  · by_contra! h
    obtain ⟨p, q, hpq⟩ := h
    have : IsAffine X.left := inferInstance
    have : DiscreteTopology (Spec Γ(X.left, ⊤)) :=
      inferInstanceAs (DiscreteTopology (PrimeSpectrum _))
    have : DiscreteTopology X.left :=
      X.left.isoSpec.schemeIsoToHomeo.isEmbedding.discreteTopology
    let U : X.left.Opens := ⟨{p}, isOpen_discrete _⟩
    have : IsClosedImmersion U.ι := by
      apply isClosedImmersion_of_isPreimmersion_of_isClosed
      simp [U]
    have : IsFiniteEtale U.ι := ⟨⟩
    have : IsFiniteEtale (U.ι ≫ X.hom) :=
      MorphismProperty.comp_mem @IsFiniteEtale _ _ ‹_› X.prop
    let i : mk (U.ι ≫ X.hom) ⟶ X := MorphismProperty.Over.homMk U.ι
    have : Mono i := (mono_iff _ _ _ i).mpr ⟨inferInstanceAs (IsOpenImmersion U.ι),
      inferInstanceAs (IsClosedImmersion U.ι)⟩
    have : IsIso i := by
      apply IsConnected.noTrivialComponent _ i
      obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.ι ≫ X.hom)
        (g := ξ k Ω) (⟨p, rfl⟩ : U) default (Subsingleton.elim (α := Spec (.of k)) _ _)
      exact not_initial_of_inhabited F (X := mk (U.ι ≫ X.hom)) z
    have : IsIso U.ι := inferInstanceAs <| IsIso ((forget _ ⋙ Over.forget _).map i)
    obtain ⟨⟨r, hr⟩, hrq⟩ := U.ι.surjective q
    simp only [U] at hr
    simp only [Scheme.Opens.ι_apply] at hrq
    exact hpq (hr.symm.trans hrq)

lemma isField_of_isConnected [IsConnected X] : IsField Γ(X.left, ⊤) := by
  obtain ⟨_, _⟩ := nonempty_and_subsingleton_of_isConnected k X
  have : IsAffine X.left := inferInstance
  let e : PrimeSpectrum Γ(X.left, ⊤) ≃ X.left :=
    X.left.isoSpec.schemeIsoToHomeo.symm.toEquiv
  have : Nonempty (PrimeSpectrum Γ(X.left, ⊤)) := e.nonempty
  have : Subsingleton (PrimeSpectrum Γ(X.left, ⊤)) := e.subsingleton
  have : Unique (PrimeSpectrum Γ(X.left, ⊤)) := uniqueOfSubsingleton (Classical.arbitrary _)
  have : Unique (MaximalSpectrum Γ(X.left, ⊤)) :=
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm.unique
  let m : MaximalSpectrum Γ(X.left, ⊤) := default
  letI : Field (Γ(X.left, ⊤) ⧸ m.asIdeal) := Ideal.Quotient.field _
  exact MulEquiv.isField (Field.toIsField _)
    ((IsArtinianRing.equivPi Γ(X.left, ⊤)).toRingEquiv.trans
      (RingEquiv.piUnique _)).toMulEquiv

noncomputable instance [IsConnected X] : Field Γ(X.left, ⊤) :=
  (isField_of_isConnected _ X).toField

/-- If `K/k` is normal, `Gal(K/k)` acts transitively on the `Spec K`-valued points of a connected
finite étale `k`-scheme. -/
instance [Normal k K] [IsConnected X] :
    MulAction.IsPretransitive (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) := by
  constructor
  intro x y
  obtain ⟨g, h⟩ := MulAction.exists_smul_eq (K ≃ₐ[k] K)
    (homEquivAlgHom k K X x) (homEquivAlgHom k K X y)
  use g
  apply (homEquivAlgHom k K X).injective
  rwa [homEquivAlgHom_smul]

/-- An isomorphism of finite étale `k`-schemes induces an isomorphism of the `k`-algebras
of global sections. -/
noncomputable
def algEquivOfIso {X Y : FiniteEtale (Spec (.of k))} (e : X ≅ Y) :
    Γ(Y.left, ⊤) ≃ₐ[k] Γ(X.left, ⊤) :=
  AlgEquiv.ofRingEquiv
    (f := (Scheme.Γ.mapIso ((forget _ ⋙ Over.forget _).mapIso e).op).commRingCatIsoToRingEquiv)
    (fun a ↦ appTop_left_algebraMap k e.hom a)

lemma algEquivOfIso_apply {X Y : FiniteEtale (Spec (.of k))} (e : X ≅ Y) (a : Γ(Y.left, ⊤)) :
    algEquivOfIso k e a = e.hom.left.appTop a :=
  rfl

/-- The global sections of a Galois object of `FiniteEtale (Spec k)` form a finite Galois
extension of `k`. -/
instance isGalois_of_isGalois [IsGalois X] : IsGalois k Γ(X.left, ⊤) := by
  let Ω : Type u := AlgebraicClosure k
  let F := fib k Ω
  have : Algebra.IsSeparable k Γ(X.left, ⊤) :=
    (Algebra.FormallyEtale.iff_isSeparable k Γ(X.left, ⊤)).mp inferInstance
  obtain ⟨x₀⟩ := nonempty_fiber_of_isConnected F X
  let e : F.obj X ≃ (Γ(X.left, ⊤) →ₐ[k] Ω) :=
    (fiberObjEquivHom (ξ k Ω) X).trans (homEquivAlgHom k Ω X)
  apply IsGalois.of_card_aut_eq_finrank
  rw [← AlgHom.natCard_of_splits k Γ(X.left, ⊤) Ω (fun _ ↦ IsAlgClosed.splits _)]
  refine Nat.card_congr (Equiv.ofBijective (fun τ ↦ (e x₀).comp τ.toAlgHom) ⟨?_, ?_⟩)
  · intro τ₁ τ₂ h
    ext a
    exact (e x₀).injective (DFunLike.congr_fun h a)
  · intro ψ
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut X) x₀ (e.symm ψ)
    refine ⟨algEquivOfIso k σ, ?_⟩
    rw [← e.apply_symm_apply ψ, ← hσ]
    ext a
    change _ = homEquivAlgHom k Ω X (fiberObjEquivHom (ξ k Ω) X (F.map σ.hom x₀)) a
    rw [← fiberObjEquivHom_naturality, homEquivAlgHom_comp]
    rfl

lemma eq_one_of_smul_eq [Algebra.IsSeparable k K] (g : K ≃ₐ[k] K)
    (H : ∀ (X : FiniteEtale (Spec (.of k))) (x : (Over.mk (ξ k K) ⟶ X.toComma)), g • x = x) :
    g = 1 := by
  ext x
  let L := IntermediateField.adjoin k {x}
  have : IsFiniteEtale (ξ k L) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
    have : Algebra.IsIntegral k L := inferInstance
    have : Module.Finite k L :=
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x)).finite_of_isAlgebraic
    have : Algebra.Etale k L :=
      ⟨.of_isSeparable k L, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    constructor
  let X : FiniteEtale (Spec (.of k)) := FiniteEtale.mk (ξ k L)
  let y : Over.mk (ξ k K) ⟶ X.toComma := by
    refine Over.homMk (Spec.map <| CommRingCat.ofHom L.subtype) ?_
    simp [X, ← Spec.map_comp, Spec.map_injective.eq_iff, ConcreteCategory.ext_iff]
  specialize H X y
  rw [CostructuredArrow.ext_iff] at H
  simp only [Over.mk_left, Subalgebra.toSubsemiring_subtype,
    IntermediateField.coe_type_toSubalgebra, algEquiv_smul_hom, Over.homMk_left, y, X] at H
  rw [← Spec.map_comp, Spec.map_injective.eq_iff, ConcreteCategory.ext_iff, RingHom.ext_iff] at H
  exact H ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩

variable [IsSepClosed K]

noncomputable
instance : MulAction (K ≃ₐ[k] K) ((forget _ ⋙ coyoneda.obj ⟨Over.mk (ξ k K)⟩).obj X) :=
  fast_instance% inferInstanceAs <| MulAction (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma)

noncomputable
instance (X : FiniteEtale (Spec (.of k))) : SMul (K ≃ₐ[k] K) ((fib k K).obj X) where
  smul g x := (fiberIsoCoyoneda (ξ k K)).inv.app X <| g • (((fiberIsoCoyoneda (ξ k K)).hom.app X) x)

lemma algEquiv_smul_fiber_def (g : K ≃ₐ[k] K) (x : (fib k K).obj X) :
    g • x = (fiberObjEquivHom (ξ k K) X).symm (g • ((fiberObjEquivHom (ξ k K) X) x)) :=
  rfl

noncomputable
instance (X : FiniteEtale (Spec (.of k))) : MulAction (K ≃ₐ[k] K) ((fib k K).obj X) where
  one_smul x := by simp [algEquiv_smul_fiber_def]
  mul_smul g h x := by simp [algEquiv_smul_fiber_def, mul_smul]

variable [IsGalois k K]

/-- If `K` is a separable closure of `k`, the absolute Galois group `Gal(K/k)` is a fundamental
group for the fiber functor of `FiniteEtale (Spec k)` at the geometric point `Spec K ⟶ Spec k`. -/
instance isFundamentalGroup : IsFundamentalGroup (fib k K) (K ≃ₐ[k] K) where
  naturality g X Y f x := by
    apply (fiberObjEquivHom (ξ k K) Y).injective
    rw [algEquiv_smul_fiber_def, algEquiv_smul_fiber_def]
    simp only [fiberObjEquivHom_symm_naturality, Equiv.apply_symm_apply]
    ext1
    simp only [Over.mk_left, Over.comp_left, algEquiv_smul_hom, Category.assoc]
    simp [← Over.comp_left, fiberObjEquivHom_naturality]
  continuous_smul X := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert stabilizer_isOpen (K ≃ₐ[k] K) (fiberObjEquivHom (ξ k K) X x) using 2
    ext g
    simp [MulAction.mem_stabilizer_iff, algEquiv_smul_fiber_def, Equiv.symm_apply_eq]
  transitive_of_isGalois X _ := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (K ≃ₐ[k] K)
      (fiberObjEquivHom _ _ x) (fiberObjEquivHom _ _ y)
    use g
    rw [algEquiv_smul_fiber_def]
    apply (fiberObjEquivHom (ξ k K) X).injective
    simp [hg]
  non_trivial' g H := by
    apply eq_one_of_smul_eq
    intro X x
    apply (fiberObjEquivHom (ξ k K) X).symm.injective
    specialize H X ((fiberObjEquivHom (ξ k K) X).symm x)
    rwa [algEquiv_smul_fiber_def, Equiv.apply_symm_apply] at H

/-- If `K` is a separable closure of `k`, the étale fundamental group of `Spec k` at the
geometric point `Spec K ⟶ Spec k` is isomorphic to the absolute Galois group `Gal(K/k)`.
This isomorphism is also a homeomorphism, see `isHomeomorph_mulEquivAutFiber`. -/
noncomputable
def mulEquivAutFiber : (K ≃ₐ[k] K) ≃* Aut (fib k K) :=
  toAutMulEquiv (fib k K) (K ≃ₐ[k] K)

lemma isHomeomorph_mulEquivAutFiber : IsHomeomorph (mulEquivAutFiber k K) :=
  toAutMulEquiv_isHomeomorph _ _

end FiniteEtale

end AlgebraicGeometry
