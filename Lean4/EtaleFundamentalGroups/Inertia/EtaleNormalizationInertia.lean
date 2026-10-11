/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.UnramifiedIntrinsicInertia
import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertia
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.RingTheory.Etale.Basic

/-!
# Original inertia of an etale normalization

Prime rigidity makes the intrinsic coefficient inertia trivial. The proved
normalization-restriction equivalence transfers this result to the original
finite-Galois inertia group, with its original action and original prime.
This is the affine implication from etaleness to condition (9) in Tag 0BTF.
No Noetherian, DVR, or henselian hypothesis is imposed.

Reference: https://stacks.math.columbia.edu/tag/0BTF
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- In an actual finite Galois normalization which is etale over its base,
the original ideal inertia at every prime is trivial. -/
theorem actualNormalizationInertia_subsingleton_of_etale
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsGalois K L] [FiniteDimensional K L]
    [Algebra.Etale A (normalizationCommAlgCat A L).carrier]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsPrime] :
    Subsingleton (actualNormalizationInertiaGroup A K L Q).carrier := by
  have : IsDomain (normalizationCommAlgCat A L).carrier :=
    subalgebraCommAlgCat_isDomain (integralClosure A L)
  have : Subsingleton
      (commAlgIdealInertiaGroup A (normalizationCommAlgCat A L) Q).carrier :=
    commAlgIdealInertia_subsingleton_of_unramified A (normalizationCommAlgCat A L) Q
  constructor
  intro σ τ
  apply (originalFiniteNormalizationInertiaEquiv A K L Q).injective
  exact Subsingleton.elim _ _

end EtaleFundamentalGroups.Inertia
