/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationResidueAction
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueDVR

/-!
# The same original residue action in quotient coordinates

This identifies its localization and quotient presentations using the
already fixed canonical maximal-quotient equivalence.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

theorem actualNormalizationResidueFieldMap_toQuotient
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A K L Q).carrier) (x : Q.ResidueField) :
    (normalizationMaximalQuotientResidueEquiv A L Q).symm.toFun
        ((actualNormalizationResidueFieldMap A K L Q d).toFun x) =
      ((actualNormalizationQuotientAction A K L Q).toFun d).toFun
        ((normalizationMaximalQuotientResidueEquiv A L Q).symm.toFun x) :=
  (maximalQuotientResidueEquiv Q).symm_apply_apply
    (((actualNormalizationQuotientAction A K L Q).toFun d).toFun
      ((normalizationMaximalQuotientResidueEquiv A L Q).symm.toFun x))

end EtaleFundamentalGroups.Inertia
