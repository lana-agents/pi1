module

public import Pi1.Orbifold.GaloisAction
public import Pi1.Orbifold.EtaleOfAlgebra
public import Pi1.Orbicurve.EtaleInertia

/-!
# Induced covers

Let `D : GaloisData k t` and let `U ⊴ H` be an open normal subgroup contained in `H_L`
(a `GaloisData.Level`), with fixed field `L_U ⊇ L` and coordinate ring `R_U`. The group `H` acts
on `R_U`. The **induced algebra** `Ind = (A → R_U)` (the algebra of `H_L`-equivariant functions
`H/U → R_U`, trivialized by a section `sec : A → H`) carries the semilinear action

  `(a • φ)(b) = (sec b · sec(a⁻¹ b)⁻¹) • φ(a⁻¹ b)`

of `A = H ⧸ H_L`. When every inertia element of `S` lies in `U`, `R_U` is étale over `R` (the
étale criterion `AffOrbicurve.etale_iff_inertia`), so `Ind` is finite étale over `R` and defines
an object `V.X` of `EquivEtale R A`, the cover of `[Spec R / A]` corresponding to the `H`-set
`H/U`. It has a distinguished fibre element `V.f₀` (evaluation at `1`), with
`σ • f₀ = f₀ ↔ σ ∈ U` (`GaloisData.Level.mem_U_of_fibreSmul_f₀`).
-/

@[expose] public section

universe u

open CategoryTheory AffOrbicurve IntermediateField.algebraAdjoinAdjoin

namespace Pi1.Orbifold

noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

namespace GaloisData

variable (D : GaloisData k t)

/-- **A level** of `D`: an open normal subgroup `U` of `H` contained in `H_L` and containing the
inertia elements `S`. -/
structure Level where
  /-- The subgroup. -/
  U : Subgroup D.H
  /-- `U` is normal in `H`. -/
  normal : U.Normal
  /-- `U` is open. -/
  isOpen : IsOpen (U : Set D.H)
  /-- `U ≤ H_L`. -/
  le : U ≤ D.HL.subgroupOf D.H
  /-- `U` contains the inertia elements. -/
  S_le : ∀ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S → σ ∈ U

namespace Level

variable {D} (V : D.Level)

/-- The subgroup `U` as a subgroup of `Gal`. -/
def Ug : Subgroup (Ω ≃ₐ[K₀ k t] Ω) := V.U.map D.H.subtype

lemma mem_Ug {σ : D.H} : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ V.Ug ↔ σ ∈ V.U :=
  Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)

lemma Ug_le : V.Ug ≤ D.HL := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact (Subgroup.mem_subgroupOf).1 (V.le hσ)

lemma isOpen_Ug : IsOpen (V.Ug : Set (Ω ≃ₐ[K₀ k t] Ω)) := by
  simp only [Ug, Subgroup.coe_map, Subgroup.coe_subtype]
  exact D.isOpen_H.isOpenMap_subtype_val _ V.isOpen

lemma isClosed_Ug : IsClosed (V.Ug : Set (Ω ≃ₐ[K₀ k t] Ω)) :=
  Subgroup.isClosed_of_isOpen _ V.isOpen_Ug

/-- The fixed field `L_U` of `U`. -/
def LU : IntermediateField (K₀ k t) Ω := IntermediateField.fixedField V.Ug

lemma L_le : D.L ≤ V.LU := IntermediateField.fixedField_le V.Ug_le

lemma stable : ∀ g ∈ D.H, ∀ x ∈ V.LU, g x ∈ V.LU := by
  refine mem_fixedField_of_normalizes fun g hg u hu => ?_
  obtain ⟨u, hu, rfl⟩ := hu
  have := V.normal.conj_mem u hu ⟨g, hg⟩⁻¹
  exact ⟨_, this, by simp⟩

/-- The coordinate ring `R_U` of `L_U`. -/
abbrev RU : Type u := CoordRing k t V.LU

instance : Algebra D.R V.RU := CoordRing.algOfLE V.L_le

instance : IsScalarTower D.R V.RU Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The action of `H` on `R_U`. -/
def actU : D.H →* RingAut V.RU := coordAut V.LU D.H V.stable

lemma algebraMap_actU (g : D.H) (x : V.RU) :
    algebraMap V.RU Ω (V.actU g x) = (g : Ω ≃ₐ[K₀ k t] Ω) (algebraMap V.RU Ω x) := rfl

lemma actU_apply_actU (g h : D.H) (x : V.RU) : V.actU g (V.actU h x) = V.actU (g * h) x := by
  rw [map_mul]; rfl

/-- **The induced algebra** `A → R_U`. -/
def Ind : Type u := D.A → V.RU

instance : CommRing V.Ind := inferInstanceAs (CommRing (D.A → V.RU))

instance : Algebra D.R V.Ind := inferInstanceAs (Algebra D.R (D.A → V.RU))

lemma algebraMap_Ind_apply (r : D.R) (b : D.A) :
    (algebraMap D.R V.Ind r : D.A → V.RU) b = algebraMap D.R V.RU r := rfl

/-- The action of `A` on the induced algebra. -/
def indSmul (a : D.A) (φ : V.Ind) : V.Ind :=
  fun b => V.actU (D.sec b * (D.sec (a⁻¹ * b))⁻¹) ((φ : D.A → V.RU) (a⁻¹ * b))

lemma indSmul_apply (a : D.A) (φ : V.Ind) (b : D.A) :
    (V.indSmul a φ : D.A → V.RU) b =
      V.actU (D.sec b * (D.sec (a⁻¹ * b))⁻¹) ((φ : D.A → V.RU) (a⁻¹ * b)) := rfl

lemma indSmul_one (φ : V.Ind) : V.indSmul 1 φ = φ := by
  funext b
  simp [indSmul_apply]

lemma indSmul_mul (a a' : D.A) (φ : V.Ind) :
    V.indSmul (a * a') φ = V.indSmul a (V.indSmul a' φ) := by
  funext b
  simp only [indSmul_apply, actU_apply_actU, mul_inv_rev, mul_assoc]
  congr 2
  group

/-- The action of `a ∈ A` on the induced algebra, as a ring automorphism. -/
def indAut (a : D.A) : V.Ind ≃+* V.Ind where
  toFun := V.indSmul a
  invFun := V.indSmul a⁻¹
  left_inv φ := by rw [← indSmul_mul, inv_mul_cancel, indSmul_one]
  right_inv φ := by rw [← indSmul_mul, mul_inv_cancel, indSmul_one]
  map_mul' φ ψ := funext fun b => map_mul (V.actU _) _ _
  map_add' φ ψ := funext fun b => map_add (V.actU _) _ _

lemma indAut_apply (a : D.A) (φ : V.Ind) : V.indAut a φ = V.indSmul a φ := rfl

/-- The lift `A →* SemilinearAut R A Ind` of the action of `A`. -/
def ρ : D.A →* SemilinearAut D.R D.A V.Ind where
  toFun a := ⟨a, V.indAut a, fun r => by
    funext b
    refine CoordRing.ext ?_
    rw [indAut_apply, indSmul_apply, algebraMap_actU, algebraMap_Ind_apply,
      algebraMap_Ind_apply]
    conv_rhs => rw [← D.mk_sec_mul_sec_inv a b]
    rfl⟩
  map_one' := SemilinearAut.ext rfl (RingEquiv.ext fun φ => V.indSmul_one φ)
  map_mul' a a' := SemilinearAut.ext rfl (RingEquiv.ext fun φ => V.indSmul_mul a a' φ)

lemma ρ_σ_apply (a : D.A) (φ : V.Ind) : (V.ρ a).σ φ = V.indSmul a φ := rfl

/-- Evaluation at `1`: the distinguished fibre element of the induced algebra. -/
def ev : V.Ind →ₐ[D.R] Ω :=
  (IsScalarTower.toAlgHom D.R V.RU Ω).comp (Pi.evalAlgHom D.R (fun _ : D.A => V.RU) 1)

lemma ev_apply (φ : V.Ind) : V.ev φ = algebraMap V.RU Ω ((φ : D.A → V.RU) 1) := rfl

section Etale

variable [IsGalois (K₀ k t) Ω]

lemma fixingSubgroup_LU : V.LU.fixingSubgroup = V.Ug :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨V.Ug, V.isClosed_Ug⟩

instance finiteDimensional_LU : FiniteDimensional (K₀ k t) V.LU :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by rw [fixingSubgroup_LU]; exact V.isOpen_Ug)

variable [CharZero k]

instance : Module.Finite D.R V.RU := module_finite_of_charZero D.transcendental V.L_le

/-- `R_U` is étale over `R`: the inertia elements fixing `L` lie in `S ⊆ U`. -/
instance : Algebra.Etale D.R V.RU := (etale_iff_inertia D.transcendental V.L_le).2 (by
  rintro W hW σ ⟨hσI, hσL⟩
  rw [SetLike.mem_coe, D.fixingSubgroup_L] at hσL
  rw [SetLike.mem_coe, V.fixingSubgroup_LU]
  exact (V.mem_Ug (σ := ⟨σ, D.le hσL⟩)).2 (V.S_le _ ⟨hσL, W, hW.1, hW.2, hσI⟩))

instance : Module.Finite D.R V.Ind := inferInstanceAs (Module.Finite D.R (D.A → V.RU))

instance : Algebra.Etale D.R V.Ind := inferInstanceAs (Algebra.Etale D.R (D.A → V.RU))

/-- **The induced cover** of `[Spec R / A]` (corresponding to the `H`-set `H/U`). -/
def X : EquivEtale D.R D.A := EquivEtale.ofAlgebra V.ρ (fun _ => rfl)

/-- The coded algebra of the induced cover is the induced algebra. -/
def e : V.X.B ≃ₐ[D.R] V.Ind := EquivEtale.ofAlgebraEquiv _ _

lemma e_act (a : D.A) (x : V.X.B) : V.e ((V.X.act a).σ x) = V.indSmul a (V.e x) :=
  EquivEtale.ofAlgebraEquiv_act _ _ a x

/-- The distinguished fibre element of the induced cover. -/
def f₀ : V.X.B →ₐ[D.R] Ω := V.ev.comp V.e.toAlgHom

lemma f₀_apply (x : V.X.B) : V.f₀ x = algebraMap V.RU Ω ((V.e x : D.A → V.RU) 1) := rfl

/-- **The action of `H` on the distinguished fibre element.** -/
lemma fibreSmul_f₀ (σ : D.H) (x : V.X.B) :
    D.fibreSmul σ V.X V.f₀ x = (σ : Ω ≃ₐ[K₀ k t] Ω)
      ((D.sec (σ : D.A) : Ω ≃ₐ[K₀ k t] Ω).symm
        (algebraMap V.RU Ω ((V.e x : D.A → V.RU) (σ : D.A)))) := by
  rw [fibreSmul_apply, f₀_apply, e_act, indSmul_apply, algebraMap_actU]
  simp

/-- **Injectivity on the induced cover**: `σ` fixes the distinguished fibre element only if
`σ ∈ U`. -/
theorem mem_U_of_fibreSmul_f₀ {σ : D.H} (h : D.fibreSmul σ V.X V.f₀ = V.f₀) : σ ∈ V.U := by
  classical
  have key : ∀ φ : V.Ind, (σ : Ω ≃ₐ[K₀ k t] Ω)
      ((D.sec (σ : D.A) : Ω ≃ₐ[K₀ k t] Ω).symm (algebraMap V.RU Ω ((φ : D.A → V.RU) (σ : D.A)))) =
        algebraMap V.RU Ω ((φ : D.A → V.RU) 1) := by
    intro φ
    have := congrArg (fun f => f (V.e.symm φ)) h
    simp only [fibreSmul_f₀, f₀_apply, AlgEquiv.apply_symm_apply] at this
    exact this
  have h1 : (σ : D.A) = 1 := by
    by_contra hne
    have := key (Pi.single 1 1 : D.A → V.RU)
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_same, map_zero, map_zero, map_zero,
      map_one] at this
    exact zero_ne_one this
  have hfix : ∀ r : V.RU, (σ : Ω ≃ₐ[K₀ k t] Ω) (algebraMap V.RU Ω r) = algebraMap V.RU Ω r := by
    intro r
    have := key (fun _ => r : D.A → V.RU)
    rwa [h1, D.sec_one, OneMemClass.coe_one, ← AlgEquiv.aut_inv, inv_one,
      AlgEquiv.one_apply] at this
  rw [← V.mem_Ug, ← V.fixingSubgroup_LU]
  exact CoordRing.mem_fixingSubgroup_of_forall _ hfix

/-- **The fibre of the induced cover is a single `H`-orbit**: every fibre element is a
translate of the distinguished one. -/
theorem exists_fibreSmul_f₀ (g : V.X.B →ₐ[D.R] Ω) : ∃ σ : D.H, D.fibreSmul σ V.X V.f₀ = g := by
  classical
  haveI := Fintype.ofFinite D.A
  let g' : V.Ind →ₐ[D.R] Ω := g.comp V.e.symm.toAlgHom
  let δ : D.A → V.Ind := fun a => (Pi.single a 1 : D.A → V.RU)
  -- a component on which `g'` is supported
  obtain ⟨a, ha⟩ : ∃ a, g' (δ a) = 1 := by
    have hsum : ∑ a, δ a = 1 := Finset.univ_sum_single (fun _ => (1 : V.RU))
    have hid : ∀ a, g' (δ a) = 0 ∨ g' (δ a) = 1 := fun a =>
      IsIdempotentElem.iff_eq_zero_or_one.1 ((show IsIdempotentElem (δ a) by
        change (Pi.single a 1 : D.A → V.RU) * Pi.single a 1 = Pi.single a 1
        rw [← Pi.single_mul, mul_one]).map g')
    by_contra hne
    push Not at hne
    have : g' (∑ a, δ a) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun a _ => (hid a).resolve_right (hne a)
    rw [hsum, map_one] at this
    exact one_ne_zero this
  -- the induced map on `R_U`
  let ψ : V.RU →+* Ω :=
    { toFun := fun y => g' (Pi.single a y : D.A → V.RU)
      map_one' := ha
      map_mul' := fun x y => by
        rw [← map_mul]
        congr 1
        exact Pi.single_mul (α := fun _ : D.A => V.RU) a x y
      map_zero' := by
        change g' (Pi.single a 0 : D.A → V.RU) = 0
        rw [Pi.single_zero]
        exact map_zero g'
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        exact Pi.single_add (f := fun _ : D.A => V.RU) a x y }
  have hψ : ∀ φ : V.Ind, g' φ = ψ ((φ : D.A → V.RU) a) := by
    intro φ
    have hφ : φ * δ a = (Pi.single a ((φ : D.A → V.RU) a) : D.A → V.RU) := by
      funext b
      change (φ : D.A → V.RU) b * (Pi.single a 1 : D.A → V.RU) b = _
      by_cases hb : b = a
      · subst hb; simp
      · simp [Pi.single_eq_of_ne hb]
    calc g' φ = g' φ * g' (δ a) := by rw [ha, mul_one]
      _ = g' (φ * δ a) := (map_mul _ _ _).symm
      _ = ψ _ := by rw [hφ]; rfl
  have hψR : ∀ r : D.R, ψ (algebraMap D.R V.RU r) = algebraMap D.R Ω r := by
    intro r
    have := hψ (algebraMap D.R V.Ind r)
    rw [AlgHom.commutes] at this
    exact this.symm
  -- `ψ` is injective
  have hinj : Function.Injective ψ := by
    haveI : Algebra.IsIntegral D.R V.RU := Algebra.IsIntegral.of_finite _ _
    have hker : (RingHom.ker ψ).comap (algebraMap D.R V.RU) = ⊥ := by
      ext r
      simp only [Ideal.mem_comap, RingHom.mem_ker, hψR, Ideal.mem_bot]
      exact ⟨fun h => CoordRing.algebraMap_injective (by rw [h, map_zero]),
        fun h => by rw [h, map_zero]⟩
    exact (RingHom.injective_iff_ker_eq_bot ψ).2 (Ideal.eq_bot_of_comap_eq_bot hker)
  -- extension to the fraction field `L_U`
  haveI := isFractionRing_coordRing t V.LU
  let ψ' : coordRing k t V.LU →+* Ω := ψ
  let ψL : V.LU →+* Ω := IsFractionRing.lift (A := coordRing k t V.LU) (g := ψ') hinj
  have hψL : ∀ y : V.RU, ψL (algebraMap (coordRing k t V.LU) V.LU y) = ψ y := fun y =>
    IsFractionRing.lift_algebraMap (A := coordRing k t V.LU) (g := ψ') hinj y
  have hfixL : ∀ y (hy : y ∈ D.L), ψL ⟨y, V.L_le hy⟩ = y := by
    intro y hy
    haveI := isFractionRing_coordRing t D.L
    obtain ⟨a', b', -, hab⟩ :=
      IsFractionRing.div_surjective (A := coordRing k t D.L) (⟨y, hy⟩ : D.L)
    have hy' := congrArg (IntermediateField.val D.L) hab
    rw [map_div₀] at hy'
    have e1 : (⟨y, V.L_le hy⟩ : V.LU) =
        algebraMap (coordRing k t V.LU) V.LU (algebraMap D.R V.RU a') /
          algebraMap (coordRing k t V.LU) V.LU (algebraMap D.R V.RU b') := by
      apply (IntermediateField.val V.LU).injective
      rw [map_div₀]
      exact hy'.symm
    rw [e1, map_div₀, hψL, hψL, hψR, hψR]
    exact hy'
  let ψK : V.LU →ₐ[K₀ k t] Ω :=
    { ψL with commutes' := fun c => hfixL (algebraMap (K₀ k t) Ω c) (D.L.algebraMap_mem c) }
  -- extension to an automorphism of `Ω`
  let τ₀ : Ω →ₐ[K₀ k t] Ω := ψK.liftNormal Ω
  let τ : Ω ≃ₐ[K₀ k t] Ω := AlgEquiv.ofBijective τ₀ (Algebra.IsAlgebraic.algHom_bijective τ₀)
  have hτ : ∀ y : V.RU, τ (algebraMap V.RU Ω y) = ψ y := fun y =>
    (AlgHom.liftNormal_commutes ψK Ω (algebraMap (coordRing k t V.LU) V.LU y)).trans (hψL y)
  have hτL : τ ∈ D.HL := by
    rw [← D.fixingSubgroup_L, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact (AlgHom.liftNormal_commutes ψK Ω ⟨y, V.L_le hy⟩).trans (hfixL y hy)
  refine ⟨⟨τ, D.le hτL⟩ * D.sec a, ?_⟩
  have hmk : ((⟨τ, D.le hτL⟩ * D.sec a : D.H) : D.A) = a := by
    rw [QuotientGroup.mk_mul, D.mk_eq_one_of_mem (σ := ⟨τ, D.le hτL⟩) hτL, one_mul, mk_sec]
  ext x
  rw [fibreSmul_f₀, hmk, Subgroup.coe_mul, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply]
  change τ _ = _
  rw [hτ, ← hψ]
  simp [g']

/-- **Domination by the induced cover**: a fibre element `f` of `X'` whose `H`-translates are
fixed by `U` is the image of the distinguished fibre element under a morphism `V.X ⟶ X'`. -/
theorem exists_hom (X' : EquivEtale D.R D.A) (f : X'.B →ₐ[D.R] Ω)
    (hf : ∀ u ∈ V.U, ∀ h : D.H,
      D.fibreSmul u X' (D.fibreSmul h X' f) = D.fibreSmul h X' f) :
    ∃ m : V.X ⟶ X', (etaleFibre D.R D.A Ω).map m V.f₀ = f := by
  have hmem : ∀ (a : D.A) (b : X'.B), D.fibreSmul (D.sec a) X' f b ∈ V.LU := by
    intro a b
    rw [LU, IntermediateField.mem_fixedField_iff]
    rintro _ ⟨u, hu, rfl⟩
    have := congrArg (fun g => g b) (hf u hu (D.sec a))
    rwa [fibreSmul_of_mem D ((Subgroup.mem_subgroupOf).1 (V.le hu))] at this
  let ψ : D.A → (X'.B →ₐ[D.R] V.RU) := fun a =>
    { toFun := fun b => CoordRing.mk (D.fibreSmul (D.sec a) X' f b) (hmem a b)
        (D.isIntegral_fibre X' _ b)
      map_one' := CoordRing.ext (by simp)
      map_mul' := fun x y => CoordRing.ext (by simp)
      map_zero' := CoordRing.ext (by simp)
      map_add' := fun x y => CoordRing.ext (by simp)
      commutes' := fun r => CoordRing.ext (by
        rw [CoordRing.algebraMap_mk, AlgHom.commutes]
        rfl) }
  have hψ : ∀ a b, algebraMap V.RU Ω (ψ a b) = D.fibreSmul (D.sec a) X' f b := fun _ _ => rfl
  let φ : X'.B →ₐ[D.R] V.Ind := AlgHom.pi ψ
  have hφ : ∀ b a, (φ b : D.A → V.RU) a = ψ a b := fun _ _ => rfl
  have hequiv : ∀ (a : D.A) (b : X'.B), φ ((X'.act a).σ b) = V.indSmul a (φ b) := by
    intro a b
    funext c
    refine CoordRing.ext ?_
    rw [hφ, hψ, indSmul_apply, algebraMap_actU, hφ, hψ, fibreSmul_apply, fibreSmul_apply,
      Subgroup.coe_mul, AlgEquiv.mul_apply, Subgroup.coe_inv, aut_inv_apply_apply]
    congr 2
    rw [QuotientGroup.mk_inv, QuotientGroup.mk_inv, mk_sec, mk_sec,
      show (a⁻¹ * c)⁻¹ = c⁻¹ * a by group, map_mul]
    rfl
  refine ⟨⟨V.e.symm.toAlgHom.comp φ, fun a y => ?_⟩, ?_⟩
  · change V.e.symm (φ ((X'.act a).σ y)) = (V.X.act a).σ (V.e.symm (φ y))
    rw [hequiv, ← ρ_σ_apply]
    exact (EquivEtale.ofAlgebraEquiv_symm_act _ _ a _).symm
  · refine AlgHom.ext fun b => ?_
    change V.f₀ (V.e.symm (φ b)) = f b
    rw [f₀_apply, AlgEquiv.apply_symm_apply, hφ, hψ, sec_one, fibreSmul_one]

end Etale

end Level

end GaloisData

end

end Pi1.Orbifold
