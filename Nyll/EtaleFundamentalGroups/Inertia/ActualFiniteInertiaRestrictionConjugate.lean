/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteDecompositionRestriction
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertiaConjugate
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealInertiaConjugate
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgInertiaConjugateRingHom
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationConjugateRingHom

/-!
# Actual finite restriction preserves original conjugation

Both restrictions project to the same constructed normalization ring map.
The group calculation is closed in its sparse full-Galois owner before
the four original and finite D/I groups occur together.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

theorem actualFiniteInertiaRestriction_conjugate
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier)
    (E : FiniteGaloisIntermediateField K L)
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualFiniteInertiaRestriction A K L Q E).hom'.toFun
        (originalFiniteNormalizationInertiaConjugate A K L Q d σ) =
      commAlgIdealInertiaConjugate A (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationPrime A K L Q E)
        ((actualFiniteDecompositionRestriction A K L Q E).hom'.toFun d)
        ((actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ) := by
  apply commAlgIdealInertiaRingHom_injective A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
  have hInv : (actualFiniteDecompositionRestriction A K L Q E).hom'.toFun (d⁻¹) =
      ((actualFiniteDecompositionRestriction A K L Q E).hom'.toFun d)⁻¹ :=
    (actualFiniteDecompositionRestriction A K L Q E).hom'.map_inv d
  exact (actualFiniteNormalizationRestrictionRingHom_conjugate A K L E d.val σ.val).trans
    ((congrArg (fun τ : (commAlgIdealDecompositionGroup A
        (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationPrime A K L Q E)).carrier =>
      (commAlgAutomorphismRingHom A (finiteAbsoluteNormalizationAlgebra A K L E)
        ((actualFiniteDecompositionRestriction A K L Q E).hom'.toFun d).val).comp
        ((commAlgIdealInertiaRingHom A (finiteAbsoluteNormalizationAlgebra A K L E)
          (finiteAbsoluteNormalizationPrime A K L Q E)
          ((actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ)).comp
          (commAlgAutomorphismRingHom A (finiteAbsoluteNormalizationAlgebra A K L E) τ.val)))
      hInv).trans
      (commAlgIdealInertiaConjugate_ringHom A (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationPrime A K L Q E)
        ((actualFiniteDecompositionRestriction A K L Q E).hom'.toFun d)
        ((actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ)).symm)

end EtaleFundamentalGroups.Inertia
