/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryLocalFixedPoint
import Nyll.EtaleFundamentalGroups.Inertia.FiniteEtaleFractionNormalizationEtale

/-!
# The actual local extension at a generic boundary point

The original boundary-unramified condition makes the normalization of every
pointed Galois fraction-stalk component étale over the DVR stalk. All point
and action comparisons are supplied by the actual cover constructions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups.Inertia

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [IsLocallyNoetherian X]
  (D : X.EffectiveCartierDivisor) (E : Component D)
  [IsDomain (X.presheaf.stalk (componentPoint D E))]
  [IsDiscreteValuationRing (X.presheaf.stalk (componentPoint D E))]
  [ConnectedSpace D.1.supportComplement]

local notation "R" => X.presheaf.stalk (componentPoint D E)
local notation "K" => FractionRing R
local notation "c" =>
  Scheme.IdealSheafData.IsEffectiveCartier.fractionStalkToSupportComplement
    (Subtype.property D) (componentPoint D E)

/-- Boundary-unramifiedness supplies an actual étale normalization of each
Galois component over the fraction field of the boundary DVR stalk. -/
theorem boundaryUnramified_localComponent_normalization_etale
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Spec (.of K))
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hU : IsBoundaryUnramified D W)
    (w : (fiber (xi ≫ c)).obj W)
    (Z : FiniteEtale (Spec (.of K))) (i : Z ⟶ (FiniteEtale.pullback c).obj W)
    (v : (fiber xi).obj Z)
    (hiv : (fiber xi).map i v =
      transportedPointOfCompIso (FiniteEtale.pullback c)
        (pullbackFiberIso c xi) W w)
    (hZ : IsGalois Z) (hi : Mono i) :
    Etale (((show Z.left ⟶ Spec (.of K) from Z.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))).fromNormalization) := by
  apply etale_fractionCover_normalization_of_geometricInertia_trivial R K Z hZ
  intro z hz τ hτ
  exact boundaryUnramified_localComponent_fixed_eq_one
    D E xi W hW hU w Z i v hiv hZ hi z hz τ hτ

end Yamaguchi26SolvableCoverings
