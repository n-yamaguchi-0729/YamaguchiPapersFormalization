/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Iso
import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideal equations from the infinity chart to the actual projective stalk

An ideal equation on the affine coordinate chart determines the equation
in every corresponding projective stalk. This isolates the chart-to-stalk
argument formerly in `IntegralSectionStalk` so that integral section ideals
and their coefficient extensions use the same actual germ comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

universe u

/-- Transport an ideal equation on the infinity chart to the actual
projective stalk by the inverse stalk map of the open immersion. -/
theorem infinityChart_stalkIdeal_eq
    (R : Type u) [CommRing R] (I : (ProjectiveLine R).IdealSheafData)
    (J : Ideal R[X])
    (htop : (I.comap (infinityChartEmbedding R)).ideal
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R[X]))⟩ =
      J.map (Scheme.ΓSpecIso (CommRingCat.of R[X])).inv.hom)
    (q : Spec (CommRingCat.of R[X])) :
    I.stalkIdeal (infinityChartEmbedding R q) = J.map (infinityChartGermAt R q) := by
  let X : Scheme := Spec (CommRingCat.of R[X])
  let j : X ⟶ ProjectiveLine R := infinityChartEmbedding R
  have : IsAffineHom j := IsAffineHom.of_comp j (ProjSpace.π R 1)
  let K : X.IdealSheafData := I.comap j
  let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let e : (ProjectiveLine R).presheaf.stalk (j q) ≅ X.presheaf.stalk q :=
    asIso ((infinityChartEmbedding R).stalkMap q)
  let g : R[X] →+* X.presheaf.stalk q :=
    ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv ≫ X.presheaf.germ ⊤ q trivial).hom
  have hK : K.stalkIdeal q = J.map g := by
    rw [K.stalkIdeal_eq_map_ideal q T (show q ∈ T.1 from trivial), htop]
    exact Ideal.map_map (Scheme.ΓSpecIso (CommRingCat.of R[X])).inv.hom
      (X.presheaf.germ ⊤ q trivial).hom
  have hstalk : (I.stalkIdeal (j q)).map e.hom.hom = J.map g := by
    change (I.stalkIdeal (j q)).map (j.stalkMap q).hom = _
    rw [← Scheme.IdealSheafData.stalkIdeal_comap_of_isAffineHom I j q]
    exact hK
  change I.stalkIdeal (j q) = _
  calc
    I.stalkIdeal (j q) = ((I.stalkIdeal (j q)).map e.hom.hom).map e.inv.hom := by
      rw [Ideal.map_map, ← CommRingCat.hom_comp, e.hom_inv_id,
        CommRingCat.hom_id, Ideal.map_id]
    _ = (J.map g).map e.inv.hom := congrArg (Ideal.map e.inv.hom) hstalk
    _ = J.map (infinityChartGermAt R q) := Ideal.map_map g e.inv.hom

end ShimizuYamaguchi26BranchedCoverings
