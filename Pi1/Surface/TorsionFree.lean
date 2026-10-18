/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
module

public import Pi1.Surface.Profinite
public import Pi1.Profinite.TorsionFree

/-!
# Profinite surface groups with a cusp are torsion-free

`Π̂_{g,r}` with `r ≥ 1` is a free profinite group (`Pi1.SurfaceGroup.profiniteFreeEquiv`), hence
torsion-free (`Pi1.Profinite.FreeHat.eq_one_of_isOfFinOrder`). In characteristic `0` this is the
torsion-freeness of the geometric fundamental group of an affine hyperbolic curve
([AbsTopI] Lemma 4.1 (iv), `Topics in Absolute Anabelian Geometry I.txt` l.2749: "X is a
hyperbolic curve if and only if Δ is torsion-free", here the "only if" for affine curves), used in
the de-cuspidalisation step `•` of [AbsTopI] Definition 4.2 (iii)(c) (l.3011–3014: the cuspidal
decomposition group must lie in "some normal open torsion-free subgroup of `Δ_j`").
-/

@[expose] public section

namespace Pi1.SurfaceGroup

open Profinite

variable {g r : ℕ}

/-- **`Π̂_{g,r}` is torsion-free for `r ≥ 1`.** -/
theorem eq_one_of_isOfFinOrder (hr : 0 < r) {z : ProfiniteSurfaceGroup g r}
    (hz : IsOfFinOrder z) : z = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  let e : ProfiniteSurfaceGroup g (r + 1) ≃* FreeHat (SurfaceGen g r) :=
    (profiniteFreeEquiv (g := g) (r := r)).toMulEquiv
  have h := FreeHat.eq_one_of_isOfFinOrder _
    ((e.injective.isOfFinOrder_iff (f := e.toMonoidHom)).2 hz)
  simpa using congrArg e.symm h

end Pi1.SurfaceGroup
