/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgStabilizerResidueMorphism
import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationDecomposition
import EtaleFundamentalGroups.Inertia.OriginalNormalizationResidueCoefficient
import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueCoefficient
import SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Residue comparison for decomposition restriction

Factors the original normalization residue morphism through decomposition restriction and the
intrinsic native residue morphism.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The same original residue morphism factors through the actual
normalization decomposition restriction and the intrinsic native residue morphism. -/
theorem originalFiniteNormalizationDecompositionMorphism_residue
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F))
    (d : normalizationDecompositionGroup A K F Q) :
    (normalizationResidueMorphism A K F Q).hom'.toFun d =
      (commAlgStabilizerResidueMorphism A (normalizationCommAlgCat A F) Q).hom'.toFun
        ((originalFiniteNormalizationDecompositionMorphism A K F Q).hom'.toFun d) := by
  apply nativeAlgebraResidueCoefficientMap_injective (normalizationCommAlgCat A F) Q
  exact (originalNormalizationResidueMorphism_coefficientMap A K F Q d).trans
    ((nativeAlgebraResidueMorphism_coefficientMap (normalizationCommAlgCat A F)
        (normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F) Q
        (commAlgAutomorphism_comp_coefficient A (normalizationCommAlgCat A F))
        ((originalFiniteNormalizationDecompositionMorphism A K F Q).hom'.toFun d)).trans
      (congrArg
        (fun f : normalizationCommAlgCat A F →+* normalizationCommAlgCat A F =>
          (Ideal.Quotient.mk Q).comp f)
        (originalFiniteNormalizationDecompositionMorphism_ringHom A K F Q d))).symm

end EtaleFundamentalGroups.Inertia

end
