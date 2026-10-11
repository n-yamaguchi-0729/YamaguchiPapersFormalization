/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelNormalizationAlgebra
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.SchemeTheory.RingTheory.Localization.CommAlgPrincipal

/-!
# Native finite normalizations at the chosen absolute prime

The existing finite-level subalgebra and normalization owners construct the
actual integral closures and their literal ring map. Prime contraction and
localization are performed on those native objects, without introducing a
second scalar action or carrying the finite field's scalar tower into the
localized ring owner.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (Ω : Type w)
  [CommRing A] [Field K] [Field Ω]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsGalois K Ω]

/-- The actual finite normalization with its native coefficient action. -/
def finiteAbsoluteNormalizationAlgebra
    (E : FiniteGaloisIntermediateField K Ω) : CommAlgCat.{w} A :=
  subalgebraNormalizationCommAlgCat (finiteLevelNormalizationSubalgebra A K Ω E)

/-- The literal finite-to-absolute normalization inclusion. -/
def finiteAbsoluteNormalizationRingMap
    (E : FiniteGaloisIntermediateField K Ω) :
    finiteAbsoluteNormalizationAlgebra A K Ω E →+* normalizationCommAlgCat A Ω :=
  subalgebraNormalizationRingMap (finiteLevelNormalizationSubalgebra A K Ω E)

omit [IsFractionRing A K] [IsGalois K Ω] in
/-- The finite normalization inclusion is injective by its existing native
normalization owner. -/
theorem finiteAbsoluteNormalizationRingMap_injective
    (E : FiniteGaloisIntermediateField K Ω) :
    Function.Injective (finiteAbsoluteNormalizationRingMap A K Ω E).toFun :=
  subalgebraNormalizationRingMap_injective (finiteLevelNormalizationSubalgebra A K Ω E)

/-- The actual contraction of the chosen absolute normalization prime. -/
def finiteAbsoluteNormalizationPrime
    (Q : Ideal (normalizationCommAlgCat A Ω))
    (E : FiniteGaloisIntermediateField K Ω) :
    Ideal (finiteAbsoluteNormalizationAlgebra A K Ω E) :=
  commAlgContractionIdeal (finiteAbsoluteNormalizationAlgebra A K Ω E)
    (normalizationCommAlgCat A Ω) (finiteAbsoluteNormalizationRingMap A K Ω E) Q

omit [IsFractionRing A K] [IsGalois K Ω] in
/-- The contracted ideal is prime because the actual coefficient map is a
ring homomorphism. -/
theorem finiteAbsoluteNormalizationPrime_isPrime
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsPrime]
    (E : FiniteGaloisIntermediateField K Ω) :
    (finiteAbsoluteNormalizationPrime A K Ω Q E).IsPrime :=
  Ideal.IsPrime.comap (finiteAbsoluteNormalizationRingMap A K Ω E)

/-- The actual localized finite normalization used by the ring-only finite
inertia character. Its data are supplied by the native localization owner. -/
def finiteAbsoluteNormalizationLocalization
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsPrime]
    (E : FiniteGaloisIntermediateField K Ω) : CommAlgCat.{w} A := by
  have : (finiteAbsoluteNormalizationPrime A K Ω Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K Ω Q E
  exact commAlgPrimeLocalization (finiteAbsoluteNormalizationAlgebra A K Ω E)
    (finiteAbsoluteNormalizationPrime A K Ω Q E)

end EtaleFundamentalGroups.Inertia

end
