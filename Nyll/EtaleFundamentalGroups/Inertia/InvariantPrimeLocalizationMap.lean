/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import Nyll.SchemeTheory.RingTheory.Localization.SubalgebraPrime
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaDiagram
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The literal inertia-invariant prime localization maps to the normalization

The fixed subalgebra is computed using the original normalization inertia
action. Its contracted-prime localization and native map to the normalization
prime localization are the already constructed generic objects and RingHoms.
The proved generic coefficient square gives the original base square directly.

The source computes the same actual localization used in 0BSU: the prime is
the comap of Q under the inclusion of its original inertia-fixed subalgebra.
No invariant/stalk comparison, alternate action, or compatibility premise is
introduced. The finite-stage image and whole invariant-image results remain
separate.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory EtaleFundamentalGroups.StrictHenselian

universe u v w

attribute [local instance] normalizationInertiaImageAction normalizationInertiaCoefficientCommClass

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (integralClosure A L))

/-- The existing actual fixed subalgebra, with its original canonical
normalization action. This closes its action data before taking localizations. -/
def normalizationInertiaFixedSubalgebra : Subalgebra A (integralClosure A L) :=
  FixedPoints.subalgebra A (integralClosure A L) (Q.inertia Gal(L/K))

variable [Q.IsPrime]

/-- The literal localization of the original inertia-fixed subalgebra at
the contraction of Q, with its native commutative ring. -/
def inertiaInvariantPrimeLocalization : CommRingCat.{w} :=
  subalgebraPrimeLocalizationSource (normalizationInertiaFixedSubalgebra A K L Q) Q

/-- The actual native localized inclusion into the original normalization
prime localization. -/
def inertiaInvariantPrimeLocalizationMap :
    inertiaInvariantPrimeLocalization A K L Q →+* Localization.AtPrime Q :=
  subalgebraPrimeLocalizationMap (normalizationInertiaFixedSubalgebra A K L Q) Q

/-- The original base map to the actual inertia-invariant localization,
computed through its genuine coefficient inclusion. -/
def inertiaInvariantPrimeLocalizationBaseMap :
    A →+* inertiaInvariantPrimeLocalization A K L Q :=
  subalgebraPrimeLocalizationBaseMap (normalizationInertiaFixedSubalgebra A K L Q) Q

/-- The native localized invariant inclusion extends precisely the original
base map to the normalization prime localization. -/
theorem inertiaInvariantPrimeLocalizationMap_comp_base :
    (inertiaInvariantPrimeLocalizationMap A K L Q).comp
        (inertiaInvariantPrimeLocalizationBaseMap A K L Q) =
      integralClosurePrimeBaseMap A L Q :=
  subalgebraPrimeLocalizationMap_comp_base
    (normalizationInertiaFixedSubalgebra A K L Q) Q

/-- The actual invariant localization with the same native algebra used by
its finite-level coefficient maps. -/
def inertiaInvariantPrimeLocalizationAlgebra : CommAlgCat.{w} A :=
  subalgebraPrimeLocalizationAlgebra (normalizationInertiaFixedSubalgebra A K L Q) Q

/-- The previously constructed base RingHom is exactly the native algebra
map on the actual invariant localization. -/
theorem inertiaInvariantPrimeLocalizationBaseMap_eq_algebraMap :
    (inertiaInvariantPrimeLocalizationBaseMap A K L Q :
        A →+* inertiaInvariantPrimeLocalizationAlgebra A K L Q) =
      algebraMap A (inertiaInvariantPrimeLocalizationAlgebra A K L Q) :=
  subalgebraPrimeLocalizationBaseMap_eq_algebraMap
    (normalizationInertiaFixedSubalgebra A K L Q) Q

end EtaleFundamentalGroups.Inertia
