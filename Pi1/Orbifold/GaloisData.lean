module

public import Pi1.Orbicurve.SubfieldGalois
public import Pi1.Orbicurve.GaloisPi1
public import Pi1.Orbifold.EtaleProfinite

/-!
# Galois data for the comparison of étale and Galois fundamental groups

Let `k` be a field, `Ω` a field over `k`, `t ∈ Ω`, `K₀ = k(t) ⊆ Ω` and
`Gal = Ω ≃ₐ[K₀] Ω`. A `GaloisData k t` consists of open subgroups `H_L ≤ H ≤ Gal` with `H_L`
normalized by `H`. It determines

* the function field `L = Ω^{H_L}` (`GaloisData.L`) and its coordinate ring `R`, the integral
  closure of `k[t]` in `L` (`GaloisData.R`);
* the finite group `A = H ⧸ H_L` (`GaloisData.A`), acting on `R` by ring automorphisms
  (`H` maps `L` to itself as it normalizes `H_L`, and `H_L` acts trivially on `L`);
* the set `S ⊆ H_L` of inertia elements at the places of `Ω` centered on `Spec R`
  (`GaloisData.S`).

The quotient orbifold `[Spec R / A]` has étale fundamental group `etalePi1 R A Ω`, which is
compared with `GaloisPi1.pi1 H S` in `Pi1.Orbifold.Comparison`.

We also record generalities on the coordinate rings `coordRing k t F`: elements are determined by
their image in `Ω` (`CoordRing.ext`), and a subgroup of `Gal` stabilizing `F` acts on
`coordRing k t F` (`coordAut`).
-/

@[expose] public section

universe u

open AffOrbicurve IntermediateField.algebraAdjoinAdjoin

namespace Pi1.Orbifold

section Coord

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

variable (k t) in
/-- The coordinate ring `coordRing k t F` (the integral closure of `k[t]` in `F`), as a type with
only the instances needed here (this keeps instance search fast). -/
def CoordRing (F : IntermediateField (K₀ k t) Ω) : Type u :=
  coordRing k t F

namespace CoordRing

variable (F : IntermediateField (K₀ k t) Ω)

instance : CommRing (CoordRing k t F) := inferInstanceAs (CommRing (coordRing k t F))
instance : IsDomain (CoordRing k t F) := inferInstanceAs (IsDomain (coordRing k t F))
instance : Algebra (CoordRing k t F) Ω := inferInstanceAs (Algebra (coordRing k t F) Ω)
instance : Algebra (A₀ k t) (CoordRing k t F) :=
  inferInstanceAs (Algebra (A₀ k t) (coordRing k t F))
instance : IsScalarTower (A₀ k t) (CoordRing k t F) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
instance : Algebra.IsIntegral (A₀ k t) (CoordRing k t F) :=
  inferInstanceAs (Algebra.IsIntegral (A₀ k t) (integralClosure (A₀ k t) F))

variable {F}

lemma ext {x y : CoordRing k t F}
    (h : algebraMap (CoordRing k t F) Ω x = algebraMap (CoordRing k t F) Ω y) : x = y :=
  Subtype.ext (Subtype.ext h)

lemma algebraMap_injective : Function.Injective (algebraMap (CoordRing k t F) Ω) :=
  fun _ _ h => ext h

lemma algebraMap_mem (x : CoordRing k t F) : algebraMap (CoordRing k t F) Ω x ∈ F :=
  (show coordRing k t F from x).1.2

lemma isIntegral_coe_iff (y : F) : IsIntegral (A₀ k t) (y : Ω) ↔ IsIntegral (A₀ k t) y :=
  isIntegral_algHom_iff ((IntermediateField.val F).restrictScalars (A₀ k t))
    (IntermediateField.val F).injective

lemma isIntegral_algebraMap (x : CoordRing k t F) :
    IsIntegral (A₀ k t) (algebraMap (CoordRing k t F) Ω x) :=
  (isIntegral_coe_iff (show coordRing k t F from x).1).2 (show coordRing k t F from x).2

/-- An element of `Ω` lying in `F` and integral over `k[t]`, as an element of the coordinate ring
of `F`. -/
def mk (x : Ω) (hF : x ∈ F) (hx : IsIntegral (A₀ k t) x) : CoordRing k t F :=
  (⟨⟨x, hF⟩, (isIntegral_coe_iff (F := F) ⟨x, hF⟩).1 hx⟩ : coordRing k t F)

@[simp] lemma algebraMap_mk (x : Ω) (hF : x ∈ F) (hx : IsIntegral (A₀ k t) x) :
    algebraMap (CoordRing k t F) Ω (mk x hF hx) = x := rfl

lemma mem_range_iff (x : Ω) : x ∈ Set.range (algebraMap (CoordRing k t F) Ω) ↔
    x ∈ F ∧ IsIntegral (A₀ k t) x :=
  ⟨by rintro ⟨y, rfl⟩; exact ⟨algebraMap_mem y, isIntegral_algebraMap y⟩,
    fun h => ⟨mk x h.1 h.2, rfl⟩⟩

/-- The inclusion `CoordRing k t F → CoordRing k t F'` for `F ≤ F'`, as an algebra structure. -/
noncomputable abbrev algOfLE {F' : IntermediateField (K₀ k t) Ω} (h : F ≤ F') :
    Algebra (CoordRing k t F) (CoordRing k t F') :=
  (ringMap t h).toRingHom.toAlgebra

lemma algebraMap_algOfLE {F' : IntermediateField (K₀ k t) Ω} (h : F ≤ F') (x : CoordRing k t F) :
    algebraMap (CoordRing k t F') Ω (@algebraMap _ _ _ _ (algOfLE h) x) =
      algebraMap (CoordRing k t F) Ω x := rfl

/-- An automorphism fixing the coordinate ring of `F` (finite over `k(t)`) fixes `F`. -/
lemma mem_fixingSubgroup_of_forall [FiniteDimensional (K₀ k t) F] (σ : Ω ≃ₐ[K₀ k t] Ω)
    (h : ∀ x : CoordRing k t F, σ (algebraMap _ Ω x) = algebraMap _ Ω x) :
    σ ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  haveI := isFractionRing_coordRing t F
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := coordRing k t F) (⟨y, hy⟩ : F)
  have hy' := congrArg (IntermediateField.val F) hab
  rw [map_div₀] at hy'
  change algebraMap (CoordRing k t F) Ω a / algebraMap (CoordRing k t F) Ω b = y at hy'
  rw [← hy', map_div₀, h a, h b]

/-- The coordinate ring is a `k`-algebra (through `k[t] ⊆ coordRing`). -/
instance algebraK (F : IntermediateField (K₀ k t) Ω) : Algebra k (CoordRing k t F) :=
  ((algebraMap (A₀ k t) (CoordRing k t F)).comp (algebraMap k (A₀ k t))).toAlgebra

instance isScalarTowerK (F : IntermediateField (K₀ k t) Ω) :
    IsScalarTower k (CoordRing k t F) Ω :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change _ = algebraMap (CoordRing k t F) Ω
      (algebraMap (A₀ k t) (CoordRing k t F) (algebraMap k (A₀ k t) c))
    rw [← IsScalarTower.algebraMap_apply]
    rfl

end CoordRing

lemma isIntegral_aut (σ : Ω ≃ₐ[K₀ k t] Ω) {x : Ω} (hx : IsIntegral (A₀ k t) x) :
    IsIntegral (A₀ k t) (σ x) :=
  hx.map ((σ : Ω →ₐ[K₀ k t] Ω).restrictScalars (A₀ k t))

/-- A subgroup `G` of `Gal` stabilizing `F` acts on the coordinate ring of `F`. -/
def coordAut (F : IntermediateField (K₀ k t) Ω) (G : Subgroup (Ω ≃ₐ[K₀ k t] Ω))
    (hG : ∀ g ∈ G, ∀ x ∈ F, g x ∈ F) : G →* RingAut (CoordRing k t F) where
  toFun g :=
    { toFun := fun x => CoordRing.mk (g.1 (algebraMap _ Ω x))
        (hG g g.2 _ (CoordRing.algebraMap_mem x))
        (isIntegral_aut _ (CoordRing.isIntegral_algebraMap x))
      invFun := fun x => CoordRing.mk (g.1⁻¹ (algebraMap _ Ω x))
        (hG _ (G.inv_mem g.2) _ (CoordRing.algebraMap_mem x))
        (isIntegral_aut _ (CoordRing.isIntegral_algebraMap x))
      left_inv := fun x => CoordRing.ext (by
        change (g.1⁻¹ * g.1) _ = _
        rw [inv_mul_cancel]; rfl)
      right_inv := fun x => CoordRing.ext (by
        change (g.1 * g.1⁻¹) _ = _
        rw [mul_inv_cancel]; rfl)
      map_mul' := fun x y => CoordRing.ext (by
        change g.1 (algebraMap _ Ω (x * y)) = g.1 (algebraMap _ Ω x) * g.1 (algebraMap _ Ω y)
        rw [map_mul, map_mul])
      map_add' := fun x y => CoordRing.ext (by
        change g.1 (algebraMap _ Ω (x + y)) = g.1 (algebraMap _ Ω x) + g.1 (algebraMap _ Ω y)
        rw [map_add, map_add]) }
  map_one' := RingEquiv.ext fun x => CoordRing.ext rfl
  map_mul' g h := RingEquiv.ext fun x => CoordRing.ext rfl

@[simp] lemma algebraMap_coordAut (F : IntermediateField (K₀ k t) Ω)
    (G : Subgroup (Ω ≃ₐ[K₀ k t] Ω)) (hG : ∀ g ∈ G, ∀ x ∈ F, g x ∈ F) (g : G)
    (x : CoordRing k t F) :
    algebraMap (CoordRing k t F) Ω (coordAut F G hG g x) = g.1 (algebraMap _ Ω x) := rfl

/-- If `G` normalizes `U`, then `G` stabilizes the fixed field of `U`. -/
lemma mem_fixedField_of_normalizes {U G : Subgroup (Ω ≃ₐ[K₀ k t] Ω)}
    (hUG : ∀ g ∈ G, ∀ u ∈ U, g⁻¹ * u * g ∈ U) :
    ∀ g ∈ G, ∀ x ∈ IntermediateField.fixedField U, g x ∈ IntermediateField.fixedField U := by
  intro g hg x hx
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro u hu
  have h := hx _ (hUG g hg u hu)
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at h
  calc u (g x) = g ((g⁻¹ : Ω ≃ₐ[K₀ k t] Ω) (u (g x))) := by simp
    _ = g x := by rw [h]

end Coord

variable (k : Type u) {Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

/-- **Galois data** for an orbifold quotient `[Spec R / A]` of the normalization `Spec R` of the
`t`-line in a finite extension of `k(t)` inside `Ω`: open subgroups `H_L ≤ H` of
`Gal(Ω / k(t))` with `H_L` normalized by `H`. -/
structure GaloisData where
  /-- The group `H` (the automorphisms of `Ω` over the function field of the coarse space). -/
  H : Subgroup (Ω ≃ₐ[K₀ k t] Ω)
  /-- The group `H_L` (the automorphisms of `Ω` over the function field `L`). -/
  HL : Subgroup (Ω ≃ₐ[K₀ k t] Ω)
  /-- `H_L ≤ H`. -/
  le : HL ≤ H
  /-- `H_L` is open. -/
  isOpen_HL : IsOpen (HL : Set (Ω ≃ₐ[K₀ k t] Ω))
  /-- `H` normalizes `H_L`. -/
  conj_mem : ∀ h ∈ H, ∀ n ∈ HL, h * n * h⁻¹ ∈ HL
  /-- `t` is transcendental over `k`. -/
  transcendental : Transcendental k t

namespace GaloisData

variable {k t} (D : GaloisData k t)

lemma isOpen_H : IsOpen (D.H : Set (Ω ≃ₐ[K₀ k t] Ω)) := Subgroup.isOpen_mono D.le D.isOpen_HL

lemma isClosed_H : IsClosed (D.H : Set (Ω ≃ₐ[K₀ k t] Ω)) :=
  Subgroup.isClosed_of_isOpen _ D.isOpen_H

lemma isClosed_HL : IsClosed (D.HL : Set (Ω ≃ₐ[K₀ k t] Ω)) :=
  Subgroup.isClosed_of_isOpen _ D.isOpen_HL

lemma conj_mem' {h : Ω ≃ₐ[K₀ k t] Ω} (hh : h ∈ D.H) {n : Ω ≃ₐ[K₀ k t] Ω} (hn : n ∈ D.HL) :
    h⁻¹ * n * h ∈ D.HL := by
  simpa using D.conj_mem h⁻¹ (D.H.inv_mem hh) n hn

/-- The function field `L = Ω^{H_L}`. -/
def L : IntermediateField (K₀ k t) Ω := IntermediateField.fixedField D.HL

/-- The coordinate ring `R = coordRing k t L` of the normalization of the `t`-line in `L`. -/
abbrev R : Type u := CoordRing k t D.L

/-- The finite group `A = H ⧸ H_L`. -/
abbrev A : Type u := D.H ⧸ D.HL.subgroupOf D.H

instance : (D.HL.subgroupOf D.H).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact D.conj_mem g g.2 n hn⟩

lemma stable : ∀ g ∈ D.H, ∀ x ∈ D.L, g x ∈ D.L :=
  mem_fixedField_of_normalizes fun _ hg _ hu => D.conj_mem' hg hu

/-- The action of `H` on `R`. -/
def actR : D.H →* RingAut D.R := coordAut D.L D.H D.stable

lemma subgroupOf_le_ker : D.HL.subgroupOf D.H ≤ D.actR.ker := by
  intro n hn
  rw [Subgroup.mem_subgroupOf] at hn
  rw [MonoidHom.mem_ker]
  refine RingEquiv.ext fun x => CoordRing.ext ?_
  change (n : Ω ≃ₐ[K₀ k t] Ω) (algebraMap D.R Ω x) = _
  exact (IntermediateField.mem_fixedField_iff _ _).1 (CoordRing.algebraMap_mem x) _ hn

/-- The action of `A = H ⧸ H_L` on `R`. -/
instance : MulSemiringAction D.A D.R :=
  MulSemiringAction.compHom _ (QuotientGroup.lift _ D.actR D.subgroupOf_le_ker)

lemma algebraMap_smul (h : D.H) (r : D.R) :
    algebraMap D.R Ω ((h : D.A) • r) = (h : Ω ≃ₐ[K₀ k t] Ω) (algebraMap D.R Ω r) := rfl

/-- The finite group `A = H ⧸ H_L` acts `k`-linearly on `R`. -/
instance smulCommClassK : SMulCommClass D.A k D.R where
  smul_comm a c r := by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    refine CoordRing.ext ?_
    rw [GaloisData.algebraMap_smul, ← IsScalarTower.algebraMap_apply]
    exact (h : Ω ≃ₐ[K₀ k t] Ω).commutes ⟨_, (K₀ k t).algebraMap_mem c⟩

/-- **The inertia elements** at the places of `Ω` centered on `Spec R`: the elements of `H_L`
lying in the inertia group of a valuation subring `W ⊆ Ω` containing `k` and `t`. -/
def S : Set (Ω ≃ₐ[K₀ k t] Ω) :=
  {σ | σ ∈ D.HL ∧ ∃ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W ∧
    σ ∈ GaloisPi1.inertia W}

lemma S_subset_HL : D.S ⊆ D.HL := fun _ h => h.1

/-- A section of `H → A = H ⧸ H_L` mapping `1` to `1`. -/
noncomputable def sec (a : D.A) : D.H := Quotient.out a * (Quotient.out (1 : D.A))⁻¹

@[simp] lemma mk_sec (a : D.A) : (D.sec a : D.A) = a := by
  simp [sec]

@[simp] lemma sec_one : D.sec 1 = 1 := mul_inv_cancel _

lemma mk_sec_mul_sec_inv (a b : D.A) : ((D.sec b * (D.sec (a⁻¹ * b))⁻¹ : D.H) : D.A) = a := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_sec, mk_sec]
  group

section Galois

variable [IsGalois (K₀ k t) Ω]

lemma fixingSubgroup_L : D.L.fixingSubgroup = D.HL :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨D.HL, D.isClosed_HL⟩

instance finiteDimensional_L : FiniteDimensional (K₀ k t) D.L :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by rw [fixingSubgroup_L]; exact D.isOpen_HL)

instance finite_A : Finite D.A :=
  Subgroup.quotient_finite_of_isOpen' D.H (D.HL.subgroupOf D.H) D.isOpen_H
    (D.isOpen_HL.preimage continuous_subtype_val)

end Galois

end GaloisData

end Pi1.Orbifold
