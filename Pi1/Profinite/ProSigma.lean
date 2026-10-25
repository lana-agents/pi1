/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.Group.Quotient
public import Pi1.Profinite.Completion

/-!
# The maximal pro-`Σ` quotient and the pro-`Σ` completion

Let `Σ` be a set of primes, given by a predicate `P : ℕ → Prop`. A natural number is a
*`Σ`-integer* (`IsSigmaNat P n`) if it is non-zero and all its prime divisors satisfy `P`. For a
topological group `G`, the *`Σ`-kernel* `sigmaKernel P G` is the intersection of the open normal
subgroups of `Σ`-integer index; the *maximal pro-`Σ` quotient* is
`MaxProSigma P G = G ⧸ sigmaKernel P G`.

Main results:
* `IsSigmaNat.mul`, `IsSigmaNat.of_dvd`, `isSigmaOpenNormal_inf`, `isSigmaOpenNormal_iInf`:
  the open normal subgroups of `Σ`-index are closed under finite intersections;
* `sigmaKernel_normal`, `isClosed_sigmaKernel`, `sigmaKernel_le_ker`: the kernel of every
  continuous homomorphism to a finite discrete group of `Σ`-integer order contains the
  `Σ`-kernel;
* for compact totally disconnected `G` (a profinite group): `MaxProSigma P G` is compact, Hausdorff
  and totally disconnected (`ProfiniteGrp.maxProSigma`), and it is **pro-`Σ`**
  (`isSigmaNat_index_maxProSigma`: every open normal subgroup has `Σ`-integer index);
* **`MaxProSigma.lift`** (with `lift_mk`, `lift_unique`): every continuous homomorphism from `G`
  to a profinite pro-`Σ` group factors uniquely through `MaxProSigma P G`;
* `ProSigmaCompletion P G` (the pro-`Σ` completion of a discrete group: the maximal pro-`Σ`
  quotient of the profinite completion), `ProSigmaCompletion.eta`, and
  **`ProSigmaCompletion.liftFinite`** (`liftFinite_eta`): homomorphisms to finite groups of
  `Σ`-integer order extend.

This is the pro-`Σ` group theory of [SemiAnbd] Ex 2.10 / Cor 3.11 (the vertex groups
`Π^Σ_{g,r}` and edge groups `Ẑ^Σ` of the pro-`Σ` semi-graph of anabelioids `G^Σ` of a stable
curve), MR12 T3.
-/

@[expose] public section

open Topology

namespace Pi1.Profinite

variable (P : ℕ → Prop)

/-- `n` is a **`Σ`-integer**: non-zero, with all prime divisors in `Σ`. -/
def IsSigmaNat (n : ℕ) : Prop := n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → P p

variable {P}

theorem isSigmaNat_one : IsSigmaNat P 1 :=
  ⟨one_ne_zero, fun _ hp h ↦ absurd (Nat.le_of_dvd one_pos h) (by have := hp.two_le; omega)⟩

theorem IsSigmaNat.mul {m n : ℕ} (hm : IsSigmaNat P m) (hn : IsSigmaNat P n) :
    IsSigmaNat P (m * n) :=
  ⟨mul_ne_zero hm.1 hn.1, fun p hp h ↦ (hp.dvd_mul.1 h).elim (hm.2 p hp) (hn.2 p hp)⟩

theorem IsSigmaNat.of_dvd {m n : ℕ} (hn : IsSigmaNat P n) (h : m ∣ n) : IsSigmaNat P m :=
  ⟨fun h0 ↦ hn.1 (Nat.eq_zero_of_zero_dvd (h0 ▸ h)), fun p hp hpm ↦ hn.2 p hp (hpm.trans h)⟩

variable (P) (G : Type*) [Group G] [TopologicalSpace G]

/-- An **open normal subgroup of `Σ`-integer index**. -/
def IsSigmaOpenNormal (N : Subgroup G) : Prop :=
  IsOpen (N : Set G) ∧ N.Normal ∧ IsSigmaNat P N.index

/-- **The `Σ`-kernel**: the intersection of the open normal subgroups of `Σ`-integer index. -/
def sigmaKernel : Subgroup G := ⨅ (N : Subgroup G) (_ : IsSigmaOpenNormal P G N), N

variable {P G}

theorem sigmaKernel_le {N : Subgroup G} (hN : IsSigmaOpenNormal P G N) : sigmaKernel P G ≤ N :=
  iInf₂_le N hN

theorem mem_sigmaKernel_iff {g : G} :
    g ∈ sigmaKernel P G ↔ ∀ N : Subgroup G, IsSigmaOpenNormal P G N → g ∈ N := by
  simp [sigmaKernel, Subgroup.mem_iInf]

instance sigmaKernel_normal : (sigmaKernel P G).Normal :=
  ⟨fun g hg h ↦
    mem_sigmaKernel_iff.2 fun N hN ↦ hN.2.1.conj_mem g (mem_sigmaKernel_iff.1 hg N hN) h⟩

theorem isClosed_sigmaKernel [IsTopologicalGroup G] : IsClosed (sigmaKernel P G : Set G) := by
  rw [sigmaKernel]
  simp only [Subgroup.coe_iInf]
  exact isClosed_iInter fun N ↦ isClosed_iInter fun hN ↦ N.isClosed_of_isOpen hN.1

theorem isSigmaOpenNormal_top : IsSigmaOpenNormal P G ⊤ :=
  ⟨isOpen_univ, inferInstance, by rw [Subgroup.index_top]; exact isSigmaNat_one⟩

theorem isSigmaOpenNormal_inf {N M : Subgroup G} (hN : IsSigmaOpenNormal P G N)
    (hM : IsSigmaOpenNormal P G M) : IsSigmaOpenNormal P G (N ⊓ M) := by
  refine ⟨hN.1.inter hM.1, @Subgroup.normal_inf_normal _ _ _ _ hN.2.1 hM.2.1, ?_⟩
  haveI := hM.2.1
  have h1 : (N ⊓ M).relIndex N * N.index = (N ⊓ M).index := Subgroup.relIndex_mul_index inf_le_left
  rw [Subgroup.inf_relIndex_left] at h1
  rw [← h1]
  exact (hM.2.2.of_dvd (Subgroup.relIndex_dvd_index_of_normal _ _)).mul hN.2.2

theorem isSigmaOpenNormal_iInf {ι : Type*} (s : Finset ι) {N : ι → Subgroup G}
    (hN : ∀ i ∈ s, IsSigmaOpenNormal P G (N i)) : IsSigmaOpenNormal P G (⨅ i ∈ s, N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSigmaOpenNormal_top
  | insert a s ha ih =>
    rw [Finset.iInf_insert]
    exact isSigmaOpenNormal_inf (hN a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hN i (Finset.mem_insert_of_mem hi))

/-- **Continuous homomorphisms to finite groups of `Σ`-integer order kill the `Σ`-kernel.** -/
theorem sigmaKernel_le_ker {Q : Type*} [Group Q] [Finite Q] [TopologicalSpace Q]
    [DiscreteTopology Q] (f : G →* Q) (hf : Continuous f) (hQ : IsSigmaNat P (Nat.card Q)) :
    sigmaKernel P G ≤ f.ker := by
  refine sigmaKernel_le ⟨?_, inferInstance, ?_⟩
  · exact (isOpen_discrete ({1} : Set Q)).preimage hf
  · rw [Subgroup.index_ker]
    exact hQ.of_dvd (Subgroup.card_subgroup_dvd_card f.range)

variable (P G) in
/-- **The maximal pro-`Σ` quotient** `G ⧸ sigmaKernel P G`. -/
abbrev MaxProSigma : Type _ := G ⧸ sigmaKernel P G

namespace MaxProSigma

/-- The quotient map `G → G^Σ`. -/
abbrev mk : G →* MaxProSigma P G := QuotientGroup.mk' _

theorem continuous_mk : Continuous (mk (P := P) (G := G)) := continuous_quot_mk

theorem mk_surjective : Function.Surjective (mk (P := P) (G := G)) := QuotientGroup.mk'_surjective _

instance [IsTopologicalGroup G] : T2Space (MaxProSigma P G) :=
  haveI : IsClosed (sigmaKernel P G : Set G) := isClosed_sigmaKernel
  inferInstance

/-- `G^Σ` is totally disconnected: points are separated by the clopen fibres of the maps to the
discrete quotients `G ⧸ N`. -/
instance [IsTopologicalGroup G] : TotallyDisconnectedSpace (MaxProSigma P G) := by
  haveI : TotallySeparatedSpace (MaxProSigma P G) := by
    rw [totallySeparatedSpace_iff_exists_isClopen]
    intro x y hxy
    obtain ⟨g, rfl⟩ := mk_surjective (P := P) x
    obtain ⟨h, rfl⟩ := mk_surjective (P := P) y
    have hgh : g⁻¹ * h ∉ sigmaKernel P G := fun hk ↦ hxy (QuotientGroup.eq.2 hk)
    obtain ⟨N, hN, hgN⟩ : ∃ N, IsSigmaOpenNormal P G N ∧ g⁻¹ * h ∉ N := by
      by_contra! H
      exact hgh (mem_sigmaKernel_iff.2 H)
    haveI := hN.2.1
    let φ : MaxProSigma P G →* G ⧸ N := QuotientGroup.map _ _ (MonoidHom.id G) (sigmaKernel_le hN)
    haveI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hN.1
    have hφ : Continuous φ := by
      refine continuous_quot_lift _ ?_
      exact continuous_quot_mk
    refine ⟨φ ⁻¹' {φ (mk g)}, (isClopen_discrete _).preimage hφ, rfl, fun hy ↦ hgN ?_⟩
    have h1 : ((h : G) : G ⧸ N) = (g : G ⧸ N) := hy
    exact QuotientGroup.eq.1 h1.symm
  infer_instance

/-- **`G^Σ` is pro-`Σ`**: for compact `G`, every open normal subgroup of `MaxProSigma P G` has
`Σ`-integer index (it contains a finite intersection of open normal subgroups of `Σ`-index, by
compactness). -/
theorem isSigmaNat_index_maxProSigma [IsTopologicalGroup G] [CompactSpace G]
    (M : Subgroup (MaxProSigma P G))
    (hM : IsOpen (M : Set (MaxProSigma P G))) : IsSigmaNat P M.index := by
  set M' := M.comap mk
  have hM' : IsOpen (M' : Set G) := hM.preimage continuous_mk
  have hidx : M'.index = M.index := Subgroup.index_comap_of_surjective _ mk_surjective
  rw [← hidx]
  have hK : sigmaKernel P G ≤ M' := fun g hg ↦ by
    have h1 : mk (P := P) g = 1 := (QuotientGroup.eq_one_iff g).2 hg
    change mk g ∈ M
    rw [h1]
    exact M.one_mem
  -- compactness: finitely many `Σ`-open normal subgroups already lie inside `M'`
  have hc : IsCompact ((M' : Set G)ᶜ) := hM'.isClosed_compl.isCompact
  have hst : ((M' : Set G)ᶜ ∩ ⋂ N : {N : Subgroup G // IsSigmaOpenNormal P G N}, (N.1 : Set G)) =
      ∅ := by
    refine Set.eq_empty_of_forall_notMem fun x ⟨hx, hx'⟩ ↦ hx (hK (mem_sigmaKernel_iff.2 ?_))
    intro N hN
    exact Set.mem_iInter.1 hx' ⟨N, hN⟩
  obtain ⟨u, hu⟩ := hc.elim_finite_subfamily_closed _
    (fun N ↦ N.1.isClosed_of_isOpen N.2.1) hst
  have hL := isSigmaOpenNormal_iInf u (N := fun N ↦ N.1) fun N _ ↦ N.2
  have hLM : (⨅ N ∈ u, N.1) ≤ M' := by
    intro x hx
    by_contra hxM
    have hx' : x ∈ ((M' : Set G)ᶜ ∩ ⋂ N ∈ u, (N.1 : Set G)) := by
      refine ⟨hxM, Set.mem_iInter₂.2 fun N hN ↦ ?_⟩
      exact (Subgroup.mem_iInf.1 hx N : x ∈ ⨅ _ : N ∈ u, N.1) |> fun h ↦
        Subgroup.mem_iInf.1 h hN
    rw [hu] at hx'
    exact hx'
  exact hL.2.2.of_dvd (Subgroup.index_dvd_of_le hLM)

/-- **Continuous homomorphisms to profinite pro-`Σ` groups kill the `Σ`-kernel.** -/
theorem sigmaKernel_le_ker_of_proSigma {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
    (hH : ∀ M : Subgroup H, IsOpen (M : Set H) → M.Normal → IsSigmaNat P M.index)
    (f : G →* H) (hf : Continuous f) : sigmaKernel P G ≤ f.ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  by_contra hfg
  haveI : T2Space H := inferInstance
  obtain ⟨M, hM⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := f g)) (Ne.symm hfg)
  have hfM : f g ∉ M := fun h ↦ hM h rfl
  have hcomap : IsSigmaOpenNormal P G (M.toSubgroup.comap f) := by
    refine ⟨M.isOpen'.preimage hf, inferInstance, ?_⟩
    rw [Subgroup.index_comap]
    exact (hH M.toSubgroup M.isOpen' inferInstance).of_dvd
      (Subgroup.relIndex_dvd_index_of_normal _ _)
  exact hfM (mem_sigmaKernel_iff.1 hg _ hcomap)

/-- **The universal property of the maximal pro-`Σ` quotient**: a continuous homomorphism to a
profinite pro-`Σ` group factors through `G^Σ`. -/
def lift {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [TotallyDisconnectedSpace H]
    (hH : ∀ M : Subgroup H, IsOpen (M : Set H) → M.Normal → IsSigmaNat P M.index)
    (f : G →* H) (hf : Continuous f) : MaxProSigma P G →* H :=
  QuotientGroup.lift _ f (sigmaKernel_le_ker_of_proSigma hH f hf)

@[simp]
theorem lift_mk {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [TotallyDisconnectedSpace H]
    (hH : ∀ M : Subgroup H, IsOpen (M : Set H) → M.Normal → IsSigmaNat P M.index)
    (f : G →* H) (hf : Continuous f) (g : G) : lift hH f hf (mk g) = f g := rfl

theorem continuous_lift {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [TotallyDisconnectedSpace H]
    (hH : ∀ M : Subgroup H, IsOpen (M : Set H) → M.Normal → IsSigmaNat P M.index)
    (f : G →* H) (hf : Continuous f) : Continuous (lift hH f hf) :=
  continuous_quot_lift _ hf

theorem lift_unique {H : Type*} [Group H] {φ ψ : MaxProSigma P G →* H}
    (h : ∀ g : G, φ (mk g) = ψ (mk g)) : φ = ψ := by
  exact QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun g ↦ h g)

/-- **The extension of a homomorphism to a finite group of `Σ`-integer order**. -/
def liftFinite {Q : Type*} [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →* Q) (hf : Continuous f) (hQ : IsSigmaNat P (Nat.card Q)) : MaxProSigma P G →* Q :=
  QuotientGroup.lift _ f (sigmaKernel_le_ker f hf hQ)

@[simp]
theorem liftFinite_mk {Q : Type*} [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →* Q) (hf : Continuous f) (hQ : IsSigmaNat P (Nat.card Q)) (g : G) :
    liftFinite f hf hQ (mk g) = f g := rfl

theorem continuous_liftFinite {Q : Type*} [Group Q] [Finite Q] [TopologicalSpace Q]
    [DiscreteTopology Q] (f : G →* Q) (hf : Continuous f) (hQ : IsSigmaNat P (Nat.card Q)) :
    Continuous (liftFinite f hf hQ) :=
  continuous_quot_lift _ hf

end MaxProSigma

variable (P G) in
/-- **The maximal pro-`Σ` quotient of a profinite group**, as a profinite group. -/
noncomputable abbrev maxProSigmaGrp [IsTopologicalGroup G] [CompactSpace G] : ProfiniteGrp :=
  ProfiniteGrp.of (MaxProSigma P G)

open ProfiniteGrp ProfiniteGrp.ProfiniteCompletion CategoryTheory

universe u

variable (P) in
/-- **The pro-`Σ` completion** of a (discrete) group: the maximal pro-`Σ` quotient of its
profinite completion. -/
noncomputable abbrev ProSigmaCompletion (Γ : Type u) [Group Γ] : Type u :=
  MaxProSigma P (completion (GrpCat.of Γ))

namespace ProSigmaCompletion

variable {Γ : Type u} [Group Γ]

variable (P) in
/-- The canonical map `Γ → Γ^Σ`. -/
noncomputable def eta : Γ →* ProSigmaCompletion P Γ :=
  (MaxProSigma.mk (P := P)).comp
    { toFun := etaFn (GrpCat.of Γ), map_one' := rfl, map_mul' := fun _ _ ↦ rfl }

/-- **Homomorphisms to finite groups of `Σ`-integer order extend** to the pro-`Σ` completion. -/
noncomputable def liftFinite {Q : Type u} [Group Q] [Finite Q] (f : Γ →* Q)
    (hQ : IsSigmaNat P (Nat.card Q)) : ProSigmaCompletion P Γ →* Q :=
  letI : TopologicalSpace Q := ⊥
  haveI : DiscreteTopology Q := ⟨rfl⟩
  MaxProSigma.liftFinite (Pi1.Profinite.liftFinite f)
    (continuous_discrete_rng.2 fun q ↦ isOpen_liftFinite_fiber f q) hQ

@[simp]
theorem liftFinite_eta {Q : Type u} [Group Q] [Finite Q] (f : Γ →* Q)
    (hQ : IsSigmaNat P (Nat.card Q)) (x : Γ) : liftFinite f hQ (eta P x) = f x :=
  Pi1.Profinite.liftFinite_eta f x

theorem denseRange_eta : DenseRange (eta P (Γ := Γ)) :=
  MaxProSigma.mk_surjective.denseRange.comp (denseRange (GrpCat.of Γ)) MaxProSigma.continuous_mk

end ProSigmaCompletion

end Pi1.Profinite
