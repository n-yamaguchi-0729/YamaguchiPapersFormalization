/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeIdealInertiaConjugate
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage

/-!
# Conjugation of original finite-field inertia

Defines the original finite-field inertia conjugate and identifies its underlying element with
the original field-automorphism expression.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

/-- The original field-inertia conjugate, with its prescribed action
closed inside the original normalization owner. -/
def originalFiniteNormalizationInertiaConjugate
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F))
    (d : normalizationDecompositionGroup A K F Q)
    (σ : actualNormalizationInertiaGroup A K F Q) :
    actualNormalizationInertiaGroup A K F Q :=
  nativeIdealInertiaConjugate (normalizationCommAlgCat A F) Gal(F/K) Q d σ

/-- The native original conjugate is exactly the original field expression. -/
theorem originalFiniteNormalizationInertiaConjugate_element
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F))
    (d : normalizationDecompositionGroup A K F Q)
    (σ : actualNormalizationInertiaGroup A K F Q) :
    actualNormalizationInertiaElement A K F Q
        (originalFiniteNormalizationInertiaConjugate A K F Q d σ) =
      (normalizationDecompositionInclusion A K F Q).toFun d *
        actualNormalizationInertiaElement A K F Q σ *
        ((normalizationDecompositionInclusion A K F Q).toFun d)⁻¹ := rfl

end EtaleFundamentalGroups.Inertia

end
