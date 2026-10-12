/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroTwoPunctures
import Nyll.AlgebraicCurves.Cohomology.Finite_H0_H1_structureSheaf_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed
import Mathlib.AlgebraicGeometry.Restrict

/-!
# The two-puncture chart from coherent genus zero

Starting from the actual structure-sheaf H¹ dimension of a smooth proper integral curve,
we construct its curve model and transport both specified punctures. The resulting scheme
isomorphism identifies their complement with the spectrum of the Laurent polynomial ring.
This geometric theorem alone does not assert the structure of its étale fundamental group.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- Over an algebraically closed field, a smooth proper integral curve of coherent genus zero
minus any two distinct closed points is isomorphic as a scheme to the Laurent polynomial chart.
There is no characteristic assumption, and neither coordinates nor a curve model are inputs. -/
theorem nonempty_laurent_iso_of_finrank_H1_eq_zero_complement_pair
    {K : Type} [Field K] [IsAlgClosed K]
    (X : Scheme.{0}) [IsIntegral X] (c : X ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (hg : Module.finrank K (𝒱.structureSheafSections c).H1 = 0)
    (x y : closedPoints X) (hne : x ≠ y)
    (U : X.Opens) (hU : (U : Set X) = {x.1, y.1}ᶜ) :
    Nonempty (U.toScheme ≅ Spec (.of (LaurentPolynomial K))) := by
  let fieldAlgebra : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
  have comparison : Module.finrank K (𝒱.structureSheafSections c).H1 =
      genusFF K X.functionField := (finite_H0_H1_structureSheaf_of_isAlgClosed 𝒱 c).2.2.2
  have genusZero : genusFF K X.functionField = 0 := comparison.symm.trans hg
  obtain ⟨fieldCurve, fieldFiniteType, M, i, _, _⟩ :=
    SmoothProperCurve.exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed K X c
  let z : closedPoints M.C := ⟨i.inv.base x.1, by
    change IsClosed ({i.inv.base x.1} : Set M.C)
    rw [← Set.image_singleton]
    exact (Scheme.homeoOfIso i.symm).isClosedMap _ x.2⟩
  let w : closedPoints M.C := ⟨i.inv.base y.1, by
    change IsClosed ({i.inv.base y.1} : Set M.C)
    rw [← Set.image_singleton]
    exact (Scheme.homeoOfIso i.symm).isClosedMap _ y.2⟩
  have hzw : z ≠ w := by
    intro heq
    apply hne
    apply Subtype.ext
    exact (Scheme.homeoOfIso i.symm).injective (congrArg Subtype.val heq)
  have hz : i.hom.base z.1 = x.1 := (Scheme.homeoOfIso i).apply_symm_apply x.1
  have hw : i.hom.base w.1 = y.1 := (Scheme.homeoOfIso i).apply_symm_apply y.1
  let V : M.C.Opens := i.hom ⁻¹ᵁ U
  have hV : (V : Set M.C) = {z.1, w.1}ᶜ := by
    apply Set.ext
    intro a
    change i.hom.base a ∈ (U : Set X) ↔ a ∉ {z.1, w.1}
    rw [hU, ← hz, ← hw]
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact not_congr (or_congr (Scheme.homeoOfIso i).injective.eq_iff
      (Scheme.homeoOfIso i).injective.eq_iff)
  obtain ⟨j⟩ := nonempty_laurent_iso_of_genus_zero_complement_pair M genusZero z w hzw V hV
  exact ⟨(i.hom.preimageIso U).symm ≪≫ j⟩

end AnabelianGeometry.GeometricFundamentalGroup
