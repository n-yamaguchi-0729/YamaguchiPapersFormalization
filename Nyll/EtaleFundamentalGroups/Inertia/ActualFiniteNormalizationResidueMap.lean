/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Residue embeddings of finite normalizations

Constructs the residue-field embedding from a finite contracted normalization prime into the
residue field of the original prime.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

/-- The canonical residue embedding at the literal finite contraction of
the original normalization prime. No infinite local valuation is required. -/
def actualFiniteNormalizationResidueMap
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat A L)) [Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    (finiteAbsoluteNormalizationPrime A K L Q E).ResidueField →+* Q.ResidueField := by
  letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact Ideal.ResidueField.map (finiteAbsoluteNormalizationPrime A K L Q E) Q
    (finiteAbsoluteNormalizationRingMap A K L E) rfl

end EtaleFundamentalGroups.Inertia

end
