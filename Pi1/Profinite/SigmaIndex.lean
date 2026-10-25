/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Σ-index subgroups of an open normal subgroup are dominated by Σ-index subgroups of the group

Let `f : H →* G` be injective with normal image of Σ-integer index (the open subgroup
`Δ_X ⊆ Δ_{E∖0}` of the Galois covering `X → E ∖ {0}`, of `ℓ`-power index). For a normal subgroup
`N ⊴ H` of finite Σ-integer index (a Galois Σ-covering of `X`), the normal core
`K = core_G (f N)` is a normal subgroup of `G` of Σ-integer index with `f⁻¹ K ≤ N`
(a Galois Σ-covering of `E ∖ {0}` dominating it). If `f` is an open embedding and `N` is open,
then `K` is open.

Here a natural number `n` is a *Σ-integer* if every prime divisor of `n` satisfies `P`.

Proof: for a prime `p ∣ [G : K]`, Cauchy gives `g ∉ K` with `g ^ p ∈ K`. If `g ∉ f H`, its image in
`G ⧸ f H` has order `p`. Otherwise some conjugate `u = k g k⁻¹ = f h` lies outside `f N`; then
`h ∉ N` and `h ^ p ∈ N`, so the image of `h` in `H ⧸ N` has order `p`.
-/

@[expose] public section

namespace Subgroup

variable {G H : Type*} [Group G] [Group H]

/-- An element outside a normal subgroup whose `p`-th power lies in it forces `p ∣` the index. -/
lemma prime_dvd_index_of_pow_mem {N : Subgroup H} [N.Normal] [N.FiniteIndex] {p : ℕ}
    (hp : p.Prime) {h : H} (hh : h ∉ N) (hhp : h ^ p ∈ N) : p ∣ N.index := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : (h : H ⧸ N) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hhp
  have h2 : (h : H ⧸ N) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  rw [index_eq_card N]
  have h3 : orderOf (h : H ⧸ N) = p := orderOf_eq_prime h1 h2
  rw [← h3]
  exact _root_.orderOf_dvd_natCard _

/-- **The prime divisors of the index of the core.** -/
theorem prime_dvd_index_normalCore_map {f : H →* G} (hf : Function.Injective f) [f.range.Normal]
    [f.range.FiniteIndex] {N : Subgroup H} [N.Normal] [N.FiniteIndex] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ (N.map f).normalCore.index) : p ∣ f.range.index ∨ p ∣ N.index := by
  haveI : Fact p.Prime := ⟨hp⟩
  set K := (N.map f).normalCore with hK
  haveI : (N.map f).FiniteIndex := ⟨by
    rw [index_map_of_injective N hf]
    exact mul_ne_zero FiniteIndex.index_ne_zero FiniteIndex.index_ne_zero⟩
  rw [index_eq_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hgp : g ^ p ∈ K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hx]
    exact pow_orderOf_eq_one _
  have hgK : g ∉ K := by
    intro hg
    have : ((g : G ⧸ K)) = 1 := (QuotientGroup.eq_one_iff g).2 hg
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hKN : K ≤ N.map f := normalCore_le _
  by_cases hg : g ∈ f.range
  · right
    have : ¬ ∀ k : G, k * g * k⁻¹ ∈ N.map f := hgK
    push Not at this
    obtain ⟨k, hk⟩ := this
    obtain ⟨h, hh⟩ : k * g * k⁻¹ ∈ f.range := Normal.conj_mem inferInstance g hg k
    have hhN : h ∉ N := fun hN => hk (hh ▸ ⟨h, hN, rfl⟩)
    have hhp : h ^ p ∈ N := by
      have hmem : k * g ^ p * k⁻¹ ∈ N.map f := hKN (Normal.conj_mem inferInstance _ hgp k)
      rw [← conj_pow, ← hh, ← map_pow] at hmem
      obtain ⟨h', hh', he⟩ := hmem
      rwa [← hf he]
    exact prime_dvd_index_of_pow_mem hp hhN hhp
  · left
    exact prime_dvd_index_of_pow_mem hp hg
      (le_trans hKN (map_le_range f N) hgp)

lemma comap_normalCore_map_le {f : H →* G} (hf : Function.Injective f) (N : Subgroup H) :
    (N.map f).normalCore.comap f ≤ N := by
  intro h hh
  obtain ⟨h', hh', he⟩ := normalCore_le _ hh
  rwa [← hf he]

lemma finiteIndex_map_of_injective {f : H →* G} (hf : Function.Injective f) [f.range.FiniteIndex]
    (N : Subgroup H) [N.FiniteIndex] : (N.map f).FiniteIndex :=
  ⟨by
    rw [index_map_of_injective N hf]
    exact mul_ne_zero FiniteIndex.index_ne_zero FiniteIndex.index_ne_zero⟩

/-- **Σ-coverings of an open normal subgroup are dominated by Σ-coverings of the group.**
For `f : H →* G` injective with normal image of Σ-integer index and `N ⊴ H` of Σ-integer index,
`K = core_G (f N)` is normal of Σ-integer index with `f⁻¹ K ≤ N`. -/
theorem sigma_index_normalCore_map (P : ℕ → Prop) {f : H →* G}
    (hf : Function.Injective f) [f.range.Normal] [f.range.FiniteIndex]
    (hfP : ∀ p, p.Prime → p ∣ f.range.index → P p) {N : Subgroup H} [N.Normal] [N.FiniteIndex]
    (hNP : ∀ p, p.Prime → p ∣ N.index → P p) :
    ∀ p, p.Prime → p ∣ (N.map f).normalCore.index → P p := by
  intro p hp hdvd
  rcases prime_dvd_index_normalCore_map hf hp hdvd with h | h
  · exact hfP p hp h
  · exact hNP p hp h

/-- **Topological form** (the form consumed by T1c): if `f` is an open embedding with normal
image of Σ-integer index, every open normal `N ⊴ H` of Σ-integer index contains `f⁻¹ K` for an
open normal `K ⊴ G` of Σ-integer index. -/
theorem exists_open_normal_comap_le_of_sigma [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace H] (P : ℕ → Prop) {f : H →* G} (hf : Topology.IsOpenEmbedding f)
    [f.range.Normal] [f.range.FiniteIndex] (hfP : ∀ p, p.Prime → p ∣ f.range.index → P p)
    {N : Subgroup H} [N.Normal] [N.FiniteIndex] (hNo : IsOpen (N : Set H))
    (hNP : ∀ p, p.Prime → p ∣ N.index → P p) :
    ∃ K : Subgroup G, K.Normal ∧ IsOpen (K : Set G) ∧ K.FiniteIndex ∧ K.comap f ≤ N ∧
      ∀ p, p.Prime → p ∣ K.index → P p := by
  haveI := finiteIndex_map_of_injective hf.injective N
  refine ⟨(N.map f).normalCore, inferInstance, ?_, inferInstance,
    comap_normalCore_map_le hf.injective N, sigma_index_normalCore_map P hf.injective hfP hNP⟩
  have hmo : IsOpen ((N.map f : Subgroup G) : Set G) := by
    rw [coe_map]; exact hf.isOpenMap _ hNo
  exact isOpen_of_isClosed_of_finiteIndex _
    (normalCore_isClosed _ (isClosed_of_isOpen _ hmo))

end Subgroup
