/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteRawTameValue
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Group.Hom.Basic

/-!
# Power normalization of finite tame values

Defines the ambient residue power map with exponent given by the ramification index divided by
the tame order, and factors the canonical coordinate through it.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]

/-- The actual e/n normalization is the standard power endomorphism of the
ambient residue monoid. It is constructed from the original index/order and
is independent of any inertia element or character value. -/
def actualFiniteTameNormalizationMap (E : FiniteGaloisIntermediateField K L) :
    Q.ResidueField →* Q.ResidueField :=
  powMonoidHom (α := Q.ResidueField)
    ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
      actualFiniteStageTameOrder A K L Q E)

/-- The SAME canonical coordinate factors through the independently
constructed raw coefficient scalar and its actual normalization operation. -/
theorem actualFiniteTameCoordinate_eq_normalizationMap
    (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    (((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val).val =
      (actualFiniteTameNormalizationMap A K L Q E).toFun
        (actualFiniteRawTameValue A K L Q E σ) :=
  actualFiniteTameCoordinate_eq_raw_pow A K L Q E σ

end EtaleFundamentalGroups.Inertia

end
