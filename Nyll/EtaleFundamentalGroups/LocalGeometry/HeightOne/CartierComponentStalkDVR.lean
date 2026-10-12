/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
import Nyll.SchemeTheory.RingTheory.RegularLocalDimensionOne
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Discrete valuation stalks at Cartier component generic points

On a locally Noetherian scheme, the generic point of an effective Cartier
divisor has codimension one. If the ambient scheme is regular along the
divisor, its stalk there is a discrete valuation ring, even when the whole
scheme is neither integral nor globally regular.

Regularity supplies the domain structure through the general regular-local
ring theorem. The component has coheight one, so the shared one-dimensional
regular-local criterion gives the DVR structure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace EtaleFundamentalGroups

/-- The local ring at a Cartier component generic point is a domain when
the ambient scheme is regular along the divisor. No global integrality of
`X` is assumed. -/
theorem isDomain_stalk_componentGenericPoint
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.1.IsAmbientRegularAlongSupport)
    (Z : Set D.1.subscheme) (hZ : Z ∈ irreducibleComponents D.1.subscheme) :
    IsDomain (X.presheaf.stalk (D.1.componentGenericPoint Z hZ)) := by
  let : IsRegularLocalRing (X.presheaf.stalk (D.1.componentGenericPoint Z hZ)) :=
    hreg.isRegularAt_componentGenericPoint Z hZ
  exact IsRegularLocalRing.isDomain (X.presheaf.stalk (D.1.componentGenericPoint Z hZ))

/-- The local ring at a generic point of an effective Cartier component is
a DVR under regularity along the divisor. Both its domain structure and its
one-dimensional regularity are obtained from the stated geometric data. -/
theorem isDiscreteValuationRing_stalk_componentGenericPoint
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.1.IsAmbientRegularAlongSupport)
    (Z : Set D.1.subscheme) (hZ : Z ∈ irreducibleComponents D.1.subscheme) :
    let : IsDomain (X.presheaf.stalk (D.1.componentGenericPoint Z hZ)) :=
      isDomain_stalk_componentGenericPoint D hreg Z hZ
    IsDiscreteValuationRing (X.presheaf.stalk (D.1.componentGenericPoint Z hZ)) := by
  intro hdomain
  let x : X := D.1.componentGenericPoint Z hZ
  let : IsRegularLocalRing (X.presheaf.stalk x) :=
    hreg.isRegularAt_componentGenericPoint Z hZ
  apply SchemeTheory.isDiscreteValuationRing_of_isRegularLocalRing_dimension_one
    (X.presheaf.stalk x)
  calc
    ringKrullDim (X.presheaf.stalk x) = (Order.coheight x : WithBot ℕ∞) :=
      ringKrullDim_stalk_eq_coheight x
    _ = (1 : WithBot ℕ∞) :=
      congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
        (D.2.coheight_componentGenericPoint_eq_one Z hZ)

end EtaleFundamentalGroups
