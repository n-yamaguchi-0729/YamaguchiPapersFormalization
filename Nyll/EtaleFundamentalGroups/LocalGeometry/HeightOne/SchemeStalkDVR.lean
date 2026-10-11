/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.HeightOne.Localization
import Nyll.SchemeTheory.Divisors.Basic

/-!
# Discrete valuation stalks at regular codimension-one points

A regular point of coheight one on an integral scheme has a discrete
valuation local ring.  This is the scheme-level entry point for divisorial
normalization and inertia results.
-/

namespace EtaleFundamentalGroups

open AlgebraicGeometry Order

universe u

/-- The stalk of an integral scheme at a regular codimension-one point is a
discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk_of_isRegularAt_of_coheight_eq_one
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    (hregular : X.IsRegularAt x) (hx : coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let : IsRegularLocalRing (X.presheaf.stalk x) := hregular
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  have hdim :
      ((Module.finrank
          (IsLocalRing.ResidueField (X.presheaf.stalk x))
          (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) : ℕ∞) :
        WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ((Module.finrank
            (IsLocalRing.ResidueField (X.presheaf.stalk x))
            (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) : ℕ∞) :
          WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk x) :=
        (IsRegularLocalRing.iff_finrank_cotangentSpace
          (X.presheaf.stalk x)).mp hregular
      _ = (coheight x : WithBot ℕ∞) :=
        AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x
      _ = ((1 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hx
  exact ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp hdim)

end EtaleFundamentalGroups
