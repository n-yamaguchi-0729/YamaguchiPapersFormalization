/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.Component
import Nyll.EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoIntegrallyClosed

/-!
# Generic finite-etale components over a two-dimensional regular local base

The normalization of a selected generic component of a finite-etale algebra
is finite etale over a normal base.  In dimension two, regular-local geometry
produces that normality internally, so it need not be supplied as an input.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uT uK uA

/-- Over a two-dimensional regular local domain, the normalization of every
specified generic component of a finite-etale algebra is finite etale. -/
theorem integralClosure_etale_genericFiberComponent_of_regularLocal_dimension_two
    {R : Type uR} {T : Type uT} {K : Type uK}
    [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (m : Ideal (T ⊗[R] K)) [m.IsMaximal] :
    Algebra.Etale R
      (integralClosure R (FiniteEtaleGenericFiberComponent m)) := by
  let : IsIntegrallyClosed R :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdim
  exact integralClosure_etale_genericFiberComponent m

/-- Height-two localization form of the selected generic-component theorem.
The normality of the localized base is source-produced from regularity and
the height equation. -/
theorem integralClosure_etale_genericFiberComponent_localizationAtPrime_of_height_eq_two
    {A : Type uA} [CommRing A] [IsDomain A] [IsRegularRing A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    {T : Type uT} {K : Type uK}
    [CommRing T] [Algebra (Localization.AtPrime P) T]
    [Module.Finite (Localization.AtPrime P) T]
    [Algebra.Etale (Localization.AtPrime P) T]
    [Field K] [Algebra (Localization.AtPrime P) K]
    [IsFractionRing (Localization.AtPrime P) K]
    (m : Ideal (T ⊗[Localization.AtPrime P] K)) [m.IsMaximal] :
    Algebra.Etale (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P)
        (FiniteEtaleGenericFiberComponent m)) := by
  let : IsIntegrallyClosed (Localization.AtPrime P) :=
    SpecialLocalPurity.isIntegrallyClosed_localizationAtPrime_of_height_eq_two
      P hP
  exact integralClosure_etale_genericFiberComponent m

end EtaleFundamentalGroups

end
