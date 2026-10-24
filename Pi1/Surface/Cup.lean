/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.H2

/-!
# Cup products and Poincaré duality in degree one for `Π̂_{g,0}`

For a topological group `G` acting trivially on a commutative group `M` of exponent dividing `n`,
the **cup product** of locally constant homomorphisms `χ : G →* M` and
`ψ : G →* Multiplicative (ZMod n)` is the class of the locally constant 2-cocycle

`(γ, δ) ↦ χ(γ) ^ ψ(δ)`   (`Pi1.Profinite.cupFun`, `Pi1.Profinite.cupClass`)

in `H²(G, M) = H2lc G M`. (This is the cocycle of `CurvesJacobian.LocAn.JacInput.cupClass`
with `M = μ_n`, so the two classes correspond under the identity on carriers.)

For `G ≃ₜ* Π̂_{g,0}` the pairing
`H¹(G, M) × H¹(G, ℤ/n) → H²(G, M) ≅ M` is **perfect**: the relator value of `χ ∪ ψ`
(the isomorphism `H²(Π̂_{g,0}, M) ≅ M` of `Pi1.SurfaceGroup.h2Equiv`) is the symplectic form

`∏ᵢ χ(aᵢ)^{ψ(bᵢ)} / χ(bᵢ)^{ψ(aᵢ)}`   (`Pi1.SurfaceGroup.relValH2Of_cupClass`),

and

* `H¹(G, M) ≅ M^{2g}` (`SurfaceGroup.hom_ext_of_isLocallyConstant`,
  `SurfaceGroup.exists_hom_eq`): locally constant homomorphisms `G →* M` are determined by their
  values at the standard generators `aᵢ, bᵢ`, and these values are arbitrary;
* the symplectic basis: `⟨aᵢ*, bⱼ*⟩ = δᵢⱼ`, `⟨aᵢ*, aⱼ*⟩ = ⟨bᵢ*, bⱼ*⟩ = 0`
  (`SurfaceGroup.relValH2Of_cupClass_dualA_dualB`, …) for the dual characters
  `SurfaceGroup.dualA`, `SurfaceGroup.dualB`;
* **the left kernel is trivial** (`SurfaceGroup.eq_of_forall_cupClass_eq`): `χ` is determined by
  the classes `χ ∪ ψ`, `ψ` running over the locally constant characters `G → ℤ/n`;
* **the right kernel is trivial** when `M` contains an element of order `n`
  (`SurfaceGroup.eq_one_of_forall_cupClass_eq_one_right`), e.g. `M = ℤ/n` or `M = μ_n`.

The cup product is bimultiplicative (`cupClass_mul_left`, `cupClass_mul_right`,
`cupClass_pow_left`), natural for continuous homomorphisms (`H2lc.comap_cupClass`, in
particular transport along `≃ₜ*`), natural in the coefficients (`cupFun_map`), and compatible
with reduction `ℤ/n → ℤ/d` for `d ∣ n` (`cupClass_castHom`). Everything is universe polymorphic in `G` and `M`.

Background: a pro-`p` group is a Demuškin group if `dim H¹(G, 𝔽_p) < ∞`, `dim H²(G, 𝔽_p) = 1` and
the cup product `H¹ × H¹ → H²` is non-degenerate ([NSW] (3.9.9)); the pro-`p` completion of the
fundamental group of a compact Riemann surface is a Poincaré group of dimension 2 ([NSW] III §7,
p. 210). The proof here is self-contained. [NSW] = Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, 2nd ed., electronic v2.3.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Topology

namespace Pi1

open SurfaceGen

namespace Profinite

/-! ### The cup-product cocycle -/

section CupFun

variable {G M M' : Type*} [Group G] [CommGroup M] [CommGroup M'] {n : ℕ}

lemma pow_mod_eq_of_pow_eq_one {m : M} (hm : m ^ n = 1) (k : ℕ) : m ^ (k % n) = m ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, hm, one_pow, mul_one]

lemma pow_zmod_val_add [NeZero n] {m : M} (hm : m ^ n = 1) (a b : ZMod n) :
    m ^ (a + b).val = m ^ a.val * m ^ b.val := by
  rw [ZMod.val_add, pow_mod_eq_of_pow_eq_one hm, pow_add]

lemma pow_zmod_val_one [NeZero n] {m : M} (hm : m ^ n = 1) : m ^ (1 : ZMod n).val = m := by
  rw [ZMod.val_one_eq_one_mod, pow_mod_eq_of_pow_eq_one hm, pow_one]

/-- The homomorphism `ℤ/n → M`, `k ↦ m ^ k`, for `m ^ n = 1`. -/
def zmodPowHom [NeZero n] {m : M} (hm : m ^ n = 1) : Multiplicative (ZMod n) →* M where
  toFun u := m ^ (Multiplicative.toAdd u).val
  map_one' := by simp
  map_mul' u v := by simp [pow_zmod_val_add hm]

@[simp] lemma zmodPowHom_apply [NeZero n] {m : M} (hm : m ^ n = 1) (u : Multiplicative (ZMod n)) :
    zmodPowHom hm u = m ^ (Multiplicative.toAdd u).val := rfl

/-- **The cup-product cocycle** `(γ, δ) ↦ χ(γ) ^ ψ(δ)` of `χ : G →* M` and
`ψ : G →* ℤ/n`. -/
def cupFun (χ : G →* M) (ψ : G →* Multiplicative (ZMod n)) : G × G → M :=
  fun p ↦ χ p.1 ^ (Multiplicative.toAdd (ψ p.2)).val

lemma cupFun_mem [NeZero n] (hM : ∀ m : M, m ^ n = 1) (χ : G →* M)
    (ψ : G →* Multiplicative (ZMod n)) : cupFun χ ψ ∈ TrivCocycle G M := fun a b c ↦ by
  simp only [cupFun, map_mul, toAdd_mul, mul_pow, pow_zmod_val_add (hM _)]
  pi1_mul_abel

/-- Naturality of the cup-product cocycle in the coefficients. -/
lemma cupFun_map (ρ : M →* M') (χ : G →* M) (ψ : G →* Multiplicative (ZMod n)) :
    ρ ∘ cupFun χ ψ = cupFun (ρ.comp χ) ψ := by
  ext p
  simp [cupFun]

/-- Reduction `ℤ/n → ℤ/d` (`d ∣ n`) as a homomorphism of multiplicative groups. -/
def zmodCastHom {d : ℕ} (hdn : d ∣ n) : Multiplicative (ZMod n) →* Multiplicative (ZMod d) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom hdn (ZMod d)).toAddMonoidHom

/-- **Compatibility across `n`**: if `M` has exponent dividing `d ∣ n`, the cup product with
`ψ : G → ℤ/n` equals the cup product with its reduction modulo `d`. -/
lemma cupFun_castHom [NeZero n] {d : ℕ} (hdn : d ∣ n) (hM : ∀ m : M, m ^ d = 1) (χ : G →* M)
    (ψ : G →* Multiplicative (ZMod n)) :
    cupFun χ ((zmodCastHom hdn).comp ψ) = cupFun χ ψ := by
  ext p
  simp only [cupFun, zmodCastHom, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.castHom_apply, toAdd_ofAdd]
  rw [ZMod.cast_eq_val, ZMod.val_natCast, pow_mod_eq_of_pow_eq_one (hM _)]

end CupFun

/-! ### The relator value of a cocycle on a commutative group -/

section RelValComm

variable {M : Type*} [CommGroup M] {k : ℕ}

/-- **On a commutative group the relator value is `∏ᵢ F(Aᵢ, Bᵢ) / F(Bᵢ, Aᵢ)`.** -/
theorem relVal_of_comm {V : Type*} [CommGroup V] (A B : Fin k → V) (F : TrivCocycle V M) :
    relVal A B F = ∏ i, F.1 (A i, B i) / F.1 (B i, A i) := by
  apply Twist.incl_injective (f := F)
  rw [← commProd_eq_incl_relVal (commProd_eq_one_of_comm A B) F (fun i ↦ ⟨1, A i⟩)
    (fun i ↦ ⟨1, B i⟩) (fun _ ↦ rfl) (fun _ ↦ rfl)]
  simp only [commProd, Twist.commutator_eq_incl]
  have h := map_list_prod (Twist.incl (f := F)) (List.ofFn fun i ↦ F.1 (A i, B i) / F.1 (B i, A i))
  rw [List.map_ofFn] at h
  rw [← List.prod_ofFn]
  exact h.symm

/-- **The relator value of the cup-product cocycle**:
`relVal(χ ∪ ψ) = ∏ᵢ χ(Aᵢ)^{ψ(Bᵢ)} / χ(Bᵢ)^{ψ(Aᵢ)}`. -/
theorem relVal_cupFun {G : Type*} [Group G] {n : ℕ} [NeZero n] (hM : ∀ m : M, m ^ n = 1)
    {A B : Fin k → G} (hAB : commProd A B = 1) (χ : G →* M) (ψ : G →* Multiplicative (ZMod n)) :
    relVal A B ⟨cupFun χ ψ, cupFun_mem hM χ ψ⟩ =
      ∏ i, χ (A i) ^ (Multiplicative.toAdd (ψ (B i))).val /
        χ (B i) ^ (Multiplicative.toAdd (ψ (A i))).val := by
  have h := relVal_comap (χ.prod ψ) hAB
    ⟨cupFun (MonoidHom.fst M _) (MonoidHom.snd _ (Multiplicative (ZMod n))),
      cupFun_mem hM _ _⟩
  exact h.trans (relVal_of_comm _ _ _)

end RelValComm

/-! ### The cup product in `H²` -/

section CupClass

variable {G G' M : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction G' M] {n : ℕ} [NeZero n]

/-- The cup-product cocycle as a locally constant 2-cocycle (trivial action). -/
def cupCocycle (htriv : ∀ (g : G) (m : M), g • m = m) (hM : ∀ m : M, m ^ n = 1) (χ : G →* M)
    (hχ : IsLocallyConstant χ) (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) :
    H2lc.cocycles G M :=
  ⟨cupFun χ ψ,
    (hχ.comp_continuous continuous_fst).comp₂ (hψ.comp_continuous continuous_snd)
      fun a b ↦ a ^ (Multiplicative.toAdd b).val,
    fun a b c ↦ by rw [htriv]; exact cupFun_mem hM χ ψ a b c⟩

@[simp] lemma coe_cupCocycle (htriv : ∀ (g : G) (m : M), g • m = m) (hM : ∀ m : M, m ^ n = 1)
    (χ : G →* M) (hχ : IsLocallyConstant χ) (ψ : G →* Multiplicative (ZMod n))
    (hψ : IsLocallyConstant ψ) :
    ((cupCocycle htriv hM χ hχ ψ hψ : H2lc.cocycles G M) : G × G → M) = cupFun χ ψ := rfl

/-- **The cup product** `χ ∪ ψ ∈ H²(G, M)` of locally constant `χ : G →* M` and
`ψ : G →* ℤ/n` (trivial action, `M` of exponent dividing `n`). -/
def cupClass (htriv : ∀ (g : G) (m : M), g • m = m) (hM : ∀ m : M, m ^ n = 1) (χ : G →* M)
    (hχ : IsLocallyConstant χ) (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) :
    H2lc G M :=
  QuotientGroup.mk (cupCocycle htriv hM χ hχ ψ hψ)

variable (htriv : ∀ (g : G) (m : M), g • m = m) (hM : ∀ m : M, m ^ n = 1)

lemma cupClass_congr {χ χ' : G →* M} (hχ : IsLocallyConstant χ) (hχ' : IsLocallyConstant χ')
    {ψ ψ' : G →* Multiplicative (ZMod n)} (hψ : IsLocallyConstant ψ)
    (hψ' : IsLocallyConstant ψ') (h₁ : χ = χ') (h₂ : ψ = ψ') :
    cupClass htriv hM χ hχ ψ hψ = cupClass htriv hM χ' hχ' ψ' hψ' := by
  subst h₁ h₂
  rfl

lemma cupClass_mul_left (χ χ' : G →* M) (hχ : IsLocallyConstant χ)
    (hχ' : IsLocallyConstant χ') (h : IsLocallyConstant (χ * χ'))
    (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) :
    cupClass htriv hM (χ * χ') h ψ hψ =
      cupClass htriv hM χ hχ ψ hψ * cupClass htriv hM χ' hχ' ψ hψ := by
  change QuotientGroup.mk _ = QuotientGroup.mk (_ * _)
  congr 1
  ext p
  simp [cupFun, mul_pow]

lemma cupClass_mul_right (χ : G →* M) (hχ : IsLocallyConstant χ)
    (ψ ψ' : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ)
    (hψ' : IsLocallyConstant ψ') (h : IsLocallyConstant (ψ * ψ')) :
    cupClass htriv hM χ hχ (ψ * ψ') h =
      cupClass htriv hM χ hχ ψ hψ * cupClass htriv hM χ hχ ψ' hψ' := by
  change QuotientGroup.mk _ = QuotientGroup.mk (_ * _)
  congr 1
  ext p
  simp [cupFun, pow_zmod_val_add (hM _)]

lemma cupClass_one_left (h : IsLocallyConstant (1 : G →* M))
    (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) :
    cupClass htriv hM 1 h ψ hψ = 1 := by
  change QuotientGroup.mk _ = QuotientGroup.mk 1
  congr 1
  ext p
  simp [cupFun]

lemma cupClass_one_right (χ : G →* M) (hχ : IsLocallyConstant χ)
    (h : IsLocallyConstant (1 : G →* Multiplicative (ZMod n))) :
    cupClass htriv hM χ hχ 1 h = 1 := by
  change QuotientGroup.mk _ = QuotientGroup.mk 1
  congr 1
  ext p
  simp [cupFun]

lemma cupClass_inv_left (χ : G →* M) (hχ : IsLocallyConstant χ) (h : IsLocallyConstant χ⁻¹)
    (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) :
    cupClass htriv hM χ⁻¹ h ψ hψ = (cupClass htriv hM χ hχ ψ hψ)⁻¹ := by
  change QuotientGroup.mk _ = QuotientGroup.mk _⁻¹
  congr 1
  ext p
  simp [cupFun, inv_pow]

lemma cupClass_pow_left (χ : G →* M) (hχ : IsLocallyConstant χ) (m : ℕ)
    (h : IsLocallyConstant (χ ^ m)) (ψ : G →* Multiplicative (ZMod n))
    (hψ : IsLocallyConstant ψ) :
    cupClass htriv hM (χ ^ m) h ψ hψ = cupClass htriv hM χ hχ ψ hψ ^ m := by
  change QuotientGroup.mk _ = QuotientGroup.mk (_ ^ m)
  congr 1
  ext p
  simp [cupFun, ← pow_mul, mul_comm]

/-- **Compatibility of the cup product with reduction `ℤ/n → ℤ/d`** (`d ∣ n`, `M` of exponent
dividing `d`). -/
lemma cupClass_castHom {d : ℕ} [NeZero d] (hdn : d ∣ n) (hMd : ∀ m : M, m ^ d = 1)
    (χ : G →* M) (hχ : IsLocallyConstant χ) (ψ : G →* Multiplicative (ZMod n))
    (hψ : IsLocallyConstant ψ) (h : IsLocallyConstant ((zmodCastHom hdn).comp ψ)) :
    cupClass htriv hMd χ hχ ((zmodCastHom hdn).comp ψ) h = cupClass htriv hM χ hχ ψ hψ := by
  change QuotientGroup.mk _ = QuotientGroup.mk _
  congr 1
  exact Subtype.ext (cupFun_castHom hdn hMd χ ψ)

/-- **Naturality of the cup product** along a continuous homomorphism `φ : G → G'` (e.g. transport
along `≃ₜ*`, or restriction to a closed subgroup). -/
lemma H2lc.comap_cupClass (φ : G →* G') (hφ : Continuous φ)
    (hact : ∀ (g : G) (m : M), φ g • m = g • m) (htriv' : ∀ (g : G') (m : M), g • m = m)
    (χ : G' →* M) (hχ : IsLocallyConstant χ) (ψ : G' →* Multiplicative (ZMod n))
    (hψ : IsLocallyConstant ψ) :
    H2lc.comap φ hφ hact (cupClass htriv' hM χ hχ ψ hψ) =
      cupClass htriv hM (χ.comp φ) (hχ.comp_continuous hφ) (ψ.comp φ)
        (hψ.comp_continuous hφ) :=
  rfl

end CupClass

/-! ### The relator value on `H²` -/

section RelValH2

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
  {k : ℕ}

/-- The relator value on locally constant cocycles (trivial action). -/
def relValCocycles {A B : Fin k → G} (hAB : commProd A B = 1)
    (htriv : ∀ (g : G) (m : M), g • m = m) : H2lc.cocycles G M →* M where
  toFun f := relVal A B ⟨f.1, mem_trivCocycle_of_mem_cocycles htriv f.2⟩
  map_one' := by
    have h := relVal_mul hAB (1 : TrivCocycle G M) 1
    rw [mul_one] at h
    exact (left_eq_mul.1 h.symm.symm).symm ▸ rfl
  map_mul' f₁ f₂ := relVal_mul hAB ⟨f₁.1, mem_trivCocycle_of_mem_cocycles htriv f₁.2⟩
    ⟨f₂.1, mem_trivCocycle_of_mem_cocycles htriv f₂.2⟩

lemma coboundaries_le_ker_relValCocycles {A B : Fin k → G} (hAB : commProd A B = 1)
    (htriv : ∀ (g : G) (m : M), g • m = m) :
    H2lc.coboundaries G M ≤ (relValCocycles hAB htriv).ker := by
  rintro f ⟨x, -, hx⟩
  rw [MonoidHom.mem_ker]
  have : (⟨f.1, mem_trivCocycle_of_mem_cocycles htriv f.2⟩ : TrivCocycle G M) =
      ⟨dxTriv x, dxTriv_mem x⟩ := by
    refine Subtype.ext ?_
    rw [← hx]
    ext ⟨γ, δ⟩
    simp [H2lc.dx, dxTriv, htriv]
  change relVal _ _ _ = 1
  rw [this]
  exact relVal_dx hAB x

/-- **The relator value `H²(G, M) → M`** at families `A, B` with `∏ᵢ [Aᵢ, Bᵢ] = 1` (trivial
action, any universes). For `G = Π̂_{g,0}` and the standard generators this is
`Pi1.SurfaceGroup.h2Equiv`. -/
def relValH2 {A B : Fin k → G} (hAB : commProd A B = 1) (htriv : ∀ (g : G) (m : M), g • m = m) :
    H2lc G M →* M :=
  QuotientGroup.lift _ (relValCocycles hAB htriv) (coboundaries_le_ker_relValCocycles hAB htriv)

lemma relValH2_mk {A B : Fin k → G} (hAB : commProd A B = 1)
    (htriv : ∀ (g : G) (m : M), g • m = m) (f : H2lc.cocycles G M) :
    relValH2 hAB htriv (QuotientGroup.mk f) =
      relVal A B ⟨f.1, mem_trivCocycle_of_mem_cocycles htriv f.2⟩ := rfl

/-- **The relator value of a cup product** is the symplectic form
`∏ᵢ χ(Aᵢ)^{ψ(Bᵢ)} / χ(Bᵢ)^{ψ(Aᵢ)}`. -/
theorem relValH2_cupClass {n : ℕ} [NeZero n] {A B : Fin k → G} (hAB : commProd A B = 1)
    (htriv : ∀ (g : G) (m : M), g • m = m) (hM : ∀ m : M, m ^ n = 1) (χ : G →* M)
    (hχ : IsLocallyConstant χ) (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) :
    relValH2 hAB htriv (cupClass htriv hM χ hχ ψ hψ) =
      ∏ i, χ (A i) ^ (Multiplicative.toAdd (ψ (B i))).val /
        χ (B i) ^ (Multiplicative.toAdd (ψ (A i))).val :=
  relVal_cupFun hM hAB χ ψ

end RelValH2

end Profinite

namespace SurfaceGroup

open Profinite

variable {g : ℕ}

/-! ### Locally constant homomorphisms out of `Π̂_{g,0}` -/

/-- **Locally constant homomorphisms out of `Π̂_{g,0}` are determined by the values at the
generators** (the image of `Π_{g,0}` is dense). -/
theorem hom_ext_of_isLocallyConstant {M : Type*} [Group M]
    {χ χ' : ProfiniteSurfaceGroup g 0 →* M} (hχ : IsLocallyConstant χ)
    (hχ' : IsLocallyConstant χ') (ha : ∀ i, χ (genAhat i) = χ' (genAhat i))
    (hb : ∀ i, χ (genBhat i) = χ' (genBhat i)) : χ = χ' := by
  have h : χ.comp (eta (GrpCat.of (SurfaceGroup g 0))).hom =
      χ'.comp (eta (GrpCat.of (SurfaceGroup g 0))).hom :=
    hom_ext (fun i ↦ ha i) (fun i ↦ hb i) (fun j ↦ j.elim0)
  ext z
  have hU : IsOpen {y | χ y = χ z ∧ χ' y = χ' z} :=
    (hχ.isOpen_fiber _).inter (hχ'.isOpen_fiber _)
  obtain ⟨x, hx⟩ := (denseRange (GrpCat.of (SurfaceGroup g 0))).exists_mem_open hU
    ⟨z, rfl, rfl⟩
  rw [← hx.1, ← hx.2]
  exact DFunLike.congr_fun h x

/-- The family `(uᵢ)` with `uᵢ = 1 ∈ ℤ/n` at `i` and `0` elsewhere. -/
abbrev unitVec (n : ℕ) (i : Fin g) : Fin g → Multiplicative (ZMod n) :=
  Pi.mulSingle i (Multiplicative.ofAdd 1)

/-- The reduction `Π̂_{g,0} → H₁(Π̂_{g,0}, ℤ/n) = (ℤ/n)^g × (ℤ/n)^g`,
`aᵢ ↦ (eᵢ, 0)`, `bᵢ ↦ (0, eᵢ)`. -/
noncomputable def abModHat (n : ℕ) [NeZero n] : ProfiniteSurfaceGroup g 0 →*
    (Fin g → Multiplicative (ZMod n)) × (Fin g → Multiplicative (ZMod n)) :=
  liftFinite (lift (fun i ↦ (unitVec n i, 1)) (fun i ↦ (1, unitVec n i)) Fin.elim0 (by
    rw [commProd_eq_one_of_comm, one_mul, ordProd, List.ofFn_zero, List.prod_nil]))

@[simp] lemma abModHat_genAhat (n : ℕ) [NeZero n] (i : Fin g) :
    abModHat n (genAhat i) = (unitVec n i, 1) := by
  simp [abModHat]

@[simp] lemma abModHat_genBhat (n : ℕ) [NeZero n] (i : Fin g) :
    abModHat n (genBhat i) = (1, unitVec n i) := by
  simp [abModHat]

lemma isLocallyConstant_abModHat (n : ℕ) [NeZero n] :
    IsLocallyConstant (abModHat (g := g) n) :=
  IsLocallyConstant.iff_isOpen_fiber.2 (isOpen_liftFinite_fiber _)

/-! ### Groups isomorphic to `Π̂_{g,0}` -/

variable {G : Type*} [Group G] [TopologicalSpace G] (e : G ≃ₜ* ProfiniteSurfaceGroup g 0)

/-- The generator `aᵢ` of `G ≃ₜ* Π̂_{g,0}`. -/
noncomputable def genAOf (i : Fin g) : G := e.symm (genAhat i)

/-- The generator `bᵢ` of `G ≃ₜ* Π̂_{g,0}`. -/
noncomputable def genBOf (i : Fin g) : G := e.symm (genBhat i)

theorem commProd_genAOf : commProd (genAOf e) (genBOf e) = 1 := by
  have h := map_commProd e.symm.toMulEquiv.toMonoidHom genAhat genBhat
  rw [commProd_genAhat, map_one] at h
  exact h.symm

/-- **Locally constant homomorphisms out of `G ≃ₜ* Π̂_{g,0}` are determined by their values at
the generators.** -/
theorem hom_ext_of_isLocallyConstant' {M : Type*} [Group M] {χ χ' : G →* M}
    (hχ : IsLocallyConstant χ) (hχ' : IsLocallyConstant χ')
    (ha : ∀ i, χ (genAOf e i) = χ' (genAOf e i)) (hb : ∀ i, χ (genBOf e i) = χ' (genBOf e i)) :
    χ = χ' := by
  have h := hom_ext_of_isLocallyConstant (χ := χ.comp e.symm.toMulEquiv.toMonoidHom)
    (χ' := χ'.comp e.symm.toMulEquiv.toMonoidHom) (hχ.comp_continuous e.symm.continuous)
    (hχ'.comp_continuous e.symm.continuous) ha hb
  ext γ
  have := DFunLike.congr_fun h (e γ)
  rwa [MonoidHom.comp_apply, MonoidHom.comp_apply,
    show e.symm.toMulEquiv.toMonoidHom (e γ) = γ from e.symm_apply_apply γ] at this

/-- The reduction `G → (ℤ/n)^g × (ℤ/n)^g` for `G ≃ₜ* Π̂_{g,0}`. -/
noncomputable def abModOf (n : ℕ) [NeZero n] :
    G →* (Fin g → Multiplicative (ZMod n)) × (Fin g → Multiplicative (ZMod n)) :=
  (abModHat n).comp e.toMulEquiv.toMonoidHom

@[simp] lemma abModOf_genAOf (n : ℕ) [NeZero n] (i : Fin g) :
    abModOf e n (genAOf e i) = (unitVec n i, 1) := by
  change abModHat n (e (e.symm (genAhat i))) = _
  rw [e.apply_symm_apply, abModHat_genAhat]

@[simp] lemma abModOf_genBOf (n : ℕ) [NeZero n] (i : Fin g) :
    abModOf e n (genBOf e i) = (1, unitVec n i) := by
  change abModHat n (e (e.symm (genBhat i))) = _
  rw [e.apply_symm_apply, abModHat_genBhat]

lemma isLocallyConstant_abModOf (n : ℕ) [NeZero n] : IsLocallyConstant (abModOf e n) :=
  (isLocallyConstant_abModHat n).comp_continuous e.continuous

/-- **The dual character `aᵢ* : G → ℤ/n`** (`aᵢ* (aⱼ) = δᵢⱼ`, `aᵢ* (bⱼ) = 0`). -/
noncomputable def dualA (n : ℕ) [NeZero n] (i : Fin g) : G →* Multiplicative (ZMod n) :=
  (Pi.evalMonoidHom _ i).comp ((MonoidHom.fst _ _).comp (abModOf e n))

/-- **The dual character `bᵢ* : G → ℤ/n`** (`bᵢ* (aⱼ) = 0`, `bᵢ* (bⱼ) = δᵢⱼ`). -/
noncomputable def dualB (n : ℕ) [NeZero n] (i : Fin g) : G →* Multiplicative (ZMod n) :=
  (Pi.evalMonoidHom _ i).comp ((MonoidHom.snd _ _).comp (abModOf e n))

variable (n : ℕ) [NeZero n]

@[simp] lemma dualA_genAOf (i j : Fin g) : dualA e n i (genAOf e j) = unitVec n j i := by
  simp [dualA]

@[simp] lemma dualA_genBOf (i j : Fin g) : dualA e n i (genBOf e j) = 1 := by
  simp [dualA]

@[simp] lemma dualB_genAOf (i j : Fin g) : dualB e n i (genAOf e j) = 1 := by
  simp [dualB]

@[simp] lemma dualB_genBOf (i j : Fin g) : dualB e n i (genBOf e j) = unitVec n j i := by
  simp [dualB]

lemma isLocallyConstant_dualA (i : Fin g) : IsLocallyConstant (dualA e n i) :=
  (isLocallyConstant_abModOf e n).comp (fun p ↦ p.1 i)

lemma isLocallyConstant_dualB (i : Fin g) : IsLocallyConstant (dualB e n i) :=
  (isLocallyConstant_abModOf e n).comp (fun p ↦ p.2 i)

/-! ### `H¹(G, M) ≅ M^{2g}` -/

variable {M : Type*} [CommGroup M] (hM : ∀ m : M, m ^ n = 1)

/-- The homomorphism `(ℤ/n)^g × (ℤ/n)^g → M`, `(u, v) ↦ ∏ⱼ xⱼ^{uⱼ} yⱼ^{vⱼ}`. -/
noncomputable def evalPairs (x y : Fin g → M) :
    (Fin g → Multiplicative (ZMod n)) × (Fin g → Multiplicative (ZMod n)) →* M :=
  ∏ j, ((zmodPowHom (hM (x j))).comp ((Pi.evalMonoidHom _ j).comp (MonoidHom.fst _ _)) *
    (zmodPowHom (hM (y j))).comp ((Pi.evalMonoidHom _ j).comp (MonoidHom.snd _ _)))

lemma toAdd_unitVec_val (i j : Fin g) {m : M} (hm : m ^ n = 1) :
    m ^ (Multiplicative.toAdd (unitVec n i j)).val = if j = i then m else 1 := by
  by_cases h : j = i
  · subst h
    simp [pow_zmod_val_one hm]
  · simp [h]

include hM in
/-- **Every family of values at the generators is realised** by a locally constant
homomorphism `G →* M`. -/
theorem exists_hom_eq (x y : Fin g → M) :
    ∃ χ : G →* M, IsLocallyConstant χ ∧ (∀ i, χ (genAOf e i) = x i) ∧
      ∀ i, χ (genBOf e i) = y i := by
  classical
  refine ⟨(evalPairs n hM x y).comp (abModOf e n), (isLocallyConstant_abModOf e n).comp _,
    fun i ↦ ?_, fun i ↦ ?_⟩
  · simp only [evalPairs, MonoidHom.comp_apply, abModOf_genAOf, MonoidHom.finsetProd_apply,
      MonoidHom.mul_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
      zmodPowHom_apply, Pi.one_apply, toAdd_one, ZMod.val_zero, pow_zero, mul_one,
      toAdd_unitVec_val n _ _ (hM _)]
    simp
  · simp only [evalPairs, MonoidHom.comp_apply, abModOf_genBOf, MonoidHom.finsetProd_apply,
      MonoidHom.mul_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
      zmodPowHom_apply, Pi.one_apply, toAdd_one, ZMod.val_zero, pow_zero, one_mul,
      toAdd_unitVec_val n _ _ (hM _)]
    simp

/-! ### The cup-product pairing on `G ≃ₜ* Π̂_{g,0}` -/

variable [MulDistribMulAction G M] (htriv : ∀ (γ : G) (m : M), γ • m = m)

/-- **The isomorphism `H²(G, M) → M`** (relator value at the generators `aᵢ, bᵢ`) for
`G ≃ₜ* Π̂_{g,0}`, trivial action, any universes; for `M : Type` finite it is
`h2EquivOfContinuousMulEquiv` (`h2EquivOfContinuousMulEquiv_apply`). -/
noncomputable def relValH2Of : H2lc G M →* M := relValH2 (commProd_genAOf e) htriv

omit hM [NeZero n] in
/-- `h2EquivOfContinuousMulEquiv` is the relator value at the generators of `G`. -/
theorem h2EquivOfContinuousMulEquiv_apply {M : Type} [CommGroup M] [Finite M] (hg : 0 < g)
    [MulDistribMulAction G M] (htriv : ∀ (γ : G) (m : M), γ • m = m) (c : H2lc G M) :
    h2EquivOfContinuousMulEquiv hg e htriv c = relValH2Of e htriv c := by
  induction c using QuotientGroup.induction_on with
  | H f =>
    letI := trivialAction (ProfiniteSurfaceGroup g 0) M
    exact relVal_comap e.symm.toMulEquiv.toMonoidHom commProd_genAhat
      ⟨f.1, mem_trivCocycle_of_mem_cocycles htriv f.2⟩

/-- **The cup-product pairing is the symplectic form**:
`(χ ∪ ψ)(relator value) = ∏ᵢ χ(aᵢ)^{ψ(bᵢ)} / χ(bᵢ)^{ψ(aᵢ)}`. -/
theorem relValH2Of_cupClass (χ : G →* M) (hχ : IsLocallyConstant χ)
    (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ) :
    relValH2Of e htriv (cupClass htriv hM χ hχ ψ hψ) =
      ∏ i, χ (genAOf e i) ^ (Multiplicative.toAdd (ψ (genBOf e i))).val /
        χ (genBOf e i) ^ (Multiplicative.toAdd (ψ (genAOf e i))).val :=
  relValH2_cupClass _ htriv hM χ hχ ψ hψ

/-- `χ ∪ bᵢ*` has relator value `χ(aᵢ)`. -/
theorem relValH2Of_cupClass_dualB (χ : G →* M) (hχ : IsLocallyConstant χ) (i : Fin g) :
    relValH2Of e htriv (cupClass htriv hM χ hχ (dualB e n i) (isLocallyConstant_dualB e n i)) =
      χ (genAOf e i) := by
  classical
  rw [relValH2Of_cupClass]
  simp only [dualB_genBOf, dualB_genAOf, toAdd_one, ZMod.val_zero, pow_zero, div_one,
    toAdd_unitVec_val n _ _ (hM _)]
  simp

/-- `χ ∪ aᵢ*` has relator value `χ(bᵢ)⁻¹`. -/
theorem relValH2Of_cupClass_dualA (χ : G →* M) (hχ : IsLocallyConstant χ) (i : Fin g) :
    relValH2Of e htriv (cupClass htriv hM χ hχ (dualA e n i) (isLocallyConstant_dualA e n i)) =
      (χ (genBOf e i))⁻¹ := by
  classical
  rw [relValH2Of_cupClass]
  simp only [dualA_genBOf, dualA_genAOf, toAdd_one, ZMod.val_zero, pow_zero,
    toAdd_unitVec_val n _ _ (hM _)]
  simp

include e in
/-- **The left kernel of the cup-product pairing is trivial**: if `χ ∪ ψ = 0` for every locally
constant `ψ : G → ℤ/n`, then `χ = 1`. -/
theorem eq_one_of_forall_cupClass_eq_one (χ : G →* M) (hχ : IsLocallyConstant χ)
    (h : ∀ (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ),
      cupClass htriv hM χ hχ ψ hψ = 1) : χ = 1 := by
  refine hom_ext_of_isLocallyConstant' e hχ (IsLocallyConstant.const 1) (fun i ↦ ?_)
    (fun i ↦ ?_)
  · have := relValH2Of_cupClass_dualB e n hM htriv χ hχ i
    rw [h, map_one] at this
    exact this.symm
  · have := relValH2Of_cupClass_dualA e n hM htriv χ hχ i
    rw [h, map_one] at this
    exact inv_eq_one.1 this.symm

include e in
/-- **Non-degeneracy in the first variable** (Poincaré duality, the form used for (P6) in MR7's
Route T′): a locally constant `χ : G →* M` is determined by the cup products `χ ∪ ψ`,
`ψ : G → ℤ/n` locally constant. -/
theorem eq_of_forall_cupClass_eq (χ χ' : G →* M) (hχ : IsLocallyConstant χ)
    (hχ' : IsLocallyConstant χ')
    (h : ∀ (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ),
      cupClass htriv hM χ hχ ψ hψ = cupClass htriv hM χ' hχ' ψ hψ) : χ = χ' := by
  have hq : IsLocallyConstant (χ * χ'⁻¹) := hχ.mul hχ'.inv
  have := eq_one_of_forall_cupClass_eq_one e n hM htriv (χ * χ'⁻¹) hq fun ψ hψ ↦ by
    rw [cupClass_mul_left htriv hM χ χ'⁻¹ hχ hχ'.inv hq,
      cupClass_inv_left htriv hM χ' hχ' hχ'.inv, h, mul_inv_cancel]
  exact mul_inv_eq_one.1 this

include e in
/-- **The right kernel of the cup-product pairing is trivial** when `M` has an element `ζ` of
order `n` (e.g. `M = ℤ/n`, or `M = μ_n` over a field containing a primitive `n`-th root of
unity): if `χ ∪ ψ = 0` for every locally constant `χ : G →* M`, then `ψ = 0`. -/
theorem eq_one_of_forall_cupClass_eq_one_right {ζ : M} (hζ : orderOf ζ = n)
    (ψ : G →* Multiplicative (ZMod n)) (hψ : IsLocallyConstant ψ)
    (h : ∀ (χ : G →* M) (hχ : IsLocallyConstant χ), cupClass htriv hM χ hχ ψ hψ = 1) :
    ψ = 1 := by
  classical
  have key (u : Multiplicative (ZMod n)) (hu : ζ ^ (Multiplicative.toAdd u).val = 1) : u = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hζ] at hu
    have hlt := ZMod.val_lt (Multiplicative.toAdd u)
    have h0 : (Multiplicative.toAdd u).val = 0 := Nat.eq_zero_of_dvd_of_lt hu hlt
    rw [ZMod.val_eq_zero] at h0
    exact h0
  refine hom_ext_of_isLocallyConstant' e hψ (IsLocallyConstant.const 1) (fun i ↦ ?_)
    (fun i ↦ ?_)
  · -- pair with `χ = ζ^{bᵢ*}`
    obtain ⟨χ, hχ, ha, hb⟩ := exists_hom_eq e n hM 1 (Pi.mulSingle i ζ)
    have := relValH2Of_cupClass e n hM htriv χ hχ ψ hψ
    rw [h, map_one] at this
    simp only [ha, hb, Pi.one_apply, one_pow, one_div] at this
    rw [Finset.prod_eq_single i (fun j _ hj ↦ by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Pi.mulSingle_eq_same, eq_comm, inv_eq_one] at this
    exact key _ this
  · -- pair with `χ = ζ^{aᵢ*}`
    obtain ⟨χ, hχ, ha, hb⟩ := exists_hom_eq e n hM (Pi.mulSingle i ζ) 1
    have := relValH2Of_cupClass e n hM htriv χ hχ ψ hψ
    rw [h, map_one] at this
    simp only [ha, hb, Pi.one_apply, one_pow, div_one] at this
    rw [Finset.prod_eq_single i (fun j _ hj ↦ by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Pi.mulSingle_eq_same, eq_comm] at this
    exact key _ this

/-! ### The symplectic basis (`M = ℤ/n`) -/

omit [NeZero n] in
lemma zmod_pow_eq_one (m : Multiplicative (ZMod n)) : m ^ n = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

variable [MulDistribMulAction G (Multiplicative (ZMod n))]
  (htriv' : ∀ (γ : G) (m : Multiplicative (ZMod n)), γ • m = m)

/-- **`⟨aᵢ*, bⱼ*⟩ = δᵢⱼ`.** -/
theorem relValH2Of_cupClass_dualA_dualB (i j : Fin g) :
    relValH2Of e htriv' (cupClass htriv' (zmod_pow_eq_one n) (dualA e n i)
      (isLocallyConstant_dualA e n i) (dualB e n j) (isLocallyConstant_dualB e n j)) =
      unitVec n j i := by
  rw [relValH2Of_cupClass_dualB, dualA_genAOf]

/-- **`⟨aᵢ*, aⱼ*⟩ = 0`.** -/
theorem relValH2Of_cupClass_dualA_dualA (i j : Fin g) :
    relValH2Of e htriv' (cupClass htriv' (zmod_pow_eq_one n) (dualA e n i)
      (isLocallyConstant_dualA e n i) (dualA e n j) (isLocallyConstant_dualA e n j)) = 1 := by
  rw [relValH2Of_cupClass_dualA, dualA_genBOf, inv_one]

/-- **`⟨bᵢ*, bⱼ*⟩ = 0`.** -/
theorem relValH2Of_cupClass_dualB_dualB (i j : Fin g) :
    relValH2Of e htriv' (cupClass htriv' (zmod_pow_eq_one n) (dualB e n i)
      (isLocallyConstant_dualB e n i) (dualB e n j) (isLocallyConstant_dualB e n j)) = 1 := by
  rw [relValH2Of_cupClass_dualB, dualB_genAOf]

/-- **`⟨bᵢ*, aⱼ*⟩ = −δᵢⱼ`.** -/
theorem relValH2Of_cupClass_dualB_dualA (i j : Fin g) :
    relValH2Of e htriv' (cupClass htriv' (zmod_pow_eq_one n) (dualB e n i)
      (isLocallyConstant_dualB e n i) (dualA e n j) (isLocallyConstant_dualA e n j)) =
      (unitVec n j i)⁻¹ := by
  rw [relValH2Of_cupClass_dualA, dualB_genBOf]

end SurfaceGroup

end Pi1
