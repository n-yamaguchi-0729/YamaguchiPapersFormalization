/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertia
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationRestriction
import EtaleFundamentalGroups.Inertia.FiniteLevelFieldAlgebra
import SchemeTheory.Normalization.NormalizationAutomorphismGroupMap
import SchemeTheory.Normalization.ScalarRestrictionGroupMap
import SchemeTheory.Normalization.NativeAutomorphismRingMaps

/-!
# Faithfulness of actual finite normalization automorphisms

Fraction-field uniqueness proves faithfulness in the native finite field
owner. The actual finite-stage map then uses that closed result.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- A native finite field automorphism is determined by its normalization. -/
theorem nativeNormalizationGaloisGroupMap_injective
    (A : Type u) (K : Type v) [CommRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (C : CommAlgCat.{w} A) (hC : IsField C.carrier)
    [Algebra K C.carrier] [IsScalarTower A K C.carrier]
    [FiniteDimensional K C.carrier] :
    Function.Injective
      (fun g : (galoisGroupObject K C.carrier).carrier =>
        (normalizationAutomorphismGroupMap A C).hom'.toFun
          ((scalarRestrictionGroupMap A K C).hom'.toFun g)) := by
  let : Field C.carrier := hC.toField
  intro σ τ hστ
  apply normalizationGaloisRingHom_injective A K C.carrier
  exact congrArg (commAlgAutomorphismRingHom A (normalizationCommAlgCat A C.carrier)) hστ

/-- The actual finite normalization restriction loses no finite Galois automorphism. -/
theorem finiteNormalizationGaloisGroupMap_injective
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) :
    Function.Injective (finiteNormalizationGaloisGroupMap A K L E).hom'.toFun :=
  nativeNormalizationGaloisGroupMap_injective A K (finiteLevelFieldAlgebra A K L E)
    (Field.toIsField (finiteLevelFieldAlgebra A K L E).carrier)

end EtaleFundamentalGroups.Inertia
