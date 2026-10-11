/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaLocalization
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaResidue
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteLocalResidue
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationResidueMap
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage

/-!
# Finite inertia and ambient residue coefficients

Proves that the localized finite inertia action fixes the coefficient map into the original
ambient residue field.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The literal actual local coefficient action also fixes its image in the
original ambient residue field. This is the proved finite residue fixedness
followed by the SAME actual residue embedding. -/
theorem actualFiniteLocalResidueMap_comp_inertia
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    (actualFiniteLocalResidueMap A K L Q E).comp
        (actualFiniteInertiaLocalRingHom A K L Q E σ) =
      actualFiniteLocalResidueMap A K L Q E := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  have hi := actualFiniteLocalResidueMap_eq_residueMap_comp A K L Q E
  have hs := actualFiniteInertiaLocalRingHom_comp_residue A K L Q E σ
  calc
    _ = ((actualFiniteNormalizationResidueMap A K L Q E).comp
          (IsLocalRing.residue
            (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)))).comp
          (actualFiniteInertiaLocalRingHom A K L Q E σ) :=
      congrArg (fun f => f.comp (actualFiniteInertiaLocalRingHom A K L Q E σ)) hi
    _ = (actualFiniteNormalizationResidueMap A K L Q E).comp
          ((IsLocalRing.residue
            (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))).comp
            (actualFiniteInertiaLocalRingHom A K L Q E σ)) := rfl
    _ = (actualFiniteNormalizationResidueMap A K L Q E).comp
          (IsLocalRing.residue
            (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))) :=
      congrArg (fun f => (actualFiniteNormalizationResidueMap A K L Q E).comp f) hs
    _ = _ := hi.symm

end EtaleFundamentalGroups.Inertia

end
