/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.SchemeTheory.Normalization.AmbientNormalizationGroupMap
import Nyll.SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueCoefficient
import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationGaloisInvariant
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Coefficients of the original residue morphism

Identifies the original normalization residue morphism with the quotient map induced by its
prescribed normalization coefficient action.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

/-- The same original normalization residue morphism is the quotient of
its prescribed normalization coefficient map. The original action is closed here. -/
theorem originalNormalizationResidueMorphism_coefficientMap
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F))
    (d : normalizationDecompositionGroup A K F Q) :
    nativeAlgebraResidueCoefficientMap (normalizationCommAlgCat A F) Q
        ((normalizationResidueMorphism A K F Q).hom'.toFun d) =
      (Ideal.Quotient.mk Q).comp (normalizationGaloisRingHom A K F d.val) := by
  exact (nativeAlgebraResidueMorphism_coefficientMap
      (normalizationCommAlgCat A F) Gal(F/K) Q
      (normalizationCommAlg_action_comp_coefficient A K F) d).trans
    (congrArg
      (fun f : normalizationCommAlgCat A F →+* normalizationCommAlgCat A F =>
        (Ideal.Quotient.mk Q).comp f)
      (normalizationGaloisRingHom_eq_original A K F d.val).symm)

end EtaleFundamentalGroups.Inertia

end
