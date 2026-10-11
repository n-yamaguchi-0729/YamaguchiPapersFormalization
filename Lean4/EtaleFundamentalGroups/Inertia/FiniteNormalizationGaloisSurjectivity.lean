/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationRestriction
import EtaleFundamentalGroups.Inertia.FiniteNormalizationActionDiagram
import SchemeTheory.Normalization.NormalizationGaloisSurjectivity
import Mathlib.Algebra.Field.IsField

/-!
# Finite normalization automorphisms have actual field lifts

The fraction-field extension theorem is applied in the native coefficient
field owner. The original ambient field does not enter that proof.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Every coefficient automorphism extends over the actual finite
fraction field. The native coefficient algebra keeps its original ring. -/
theorem nativeNormalizationGaloisGroupMap_surjective
    (A : Type u) (K : Type v) [CommRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (C : CommAlgCat.{w} A) (hC : IsField C.carrier)
    [Algebra K C.carrier] [IsScalarTower A K C.carrier]
    [FiniteDimensional K C.carrier] :
    Function.Surjective
      (fun g : (galoisGroupObject K C.carrier).carrier =>
        (normalizationAutomorphismGroupMap A C).hom'.toFun
          ((scalarRestrictionGroupMap A K C).hom'.toFun g)) := by
  let : Field C.carrier := hC.toField
  exact normalizationGaloisGroupMap_surjective A K C.carrier

/-- The original finite-normalization group map has all intrinsic
coefficient automorphisms in its image. -/
theorem finiteNormalizationGaloisGroupMap_surjective
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) :
    Function.Surjective (finiteNormalizationGaloisGroupMap A K L E).hom'.toFun :=
  nativeNormalizationGaloisGroupMap_surjective A K (finiteLevelFieldAlgebra A K L E)
    (finiteGaloisIntermediateField_isField K L E)

end EtaleFundamentalGroups.Inertia
