/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
import Nyll.SchemeTheory.Divisors.CartierEtale
import Nyll.SchemeTheory.Divisors.ConnectedComplement
import Nyll.SchemeTheory.Divisors.EtaleRegularity
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenImmersionPullbackModel
import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective

/-!
# Connectedness across a regular Cartier boundary

Regularity is required only along the boundary.  Applying connectedness of
Cartier complements to each connected finite étale cover proves the
surjectivity assertion of Lemma 1.1 by the connected-object criterion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X : Scheme.{u}} [ConnectedSpace X] [IsLocallyNoetherian X]

/-- Removing a Cartier boundary with regular ambient stalks preserves connectedness. -/
theorem boundaryComplement_connectedSpace
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport) :
    ConnectedSpace D.1.supportComplement := by
  apply D.connectedSpace_supportComplement_of_domain_stalks
  intro x hx
  let : IsRegularLocalRing (X.presheaf.stalk x) := hreg x hx
  exact IsRegularLocalRing.isDomain (X.presheaf.stalk x)

/-- Connected finite étale covers remain connected on the boundary complement. -/
theorem boundaryComplement_pullback_isConnected
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    (W : FiniteEtale X) [IsConnected W] :
    IsConnected ((pullback D.1.supportComplement.ι).obj W) := by
  let : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  let f : W.left ⟶ X := W.hom
  let : IsFiniteEtale f := W.prop
  let : IsLocallyNoetherian W.left :=
    LocallyOfFiniteType.isLocallyNoetherian f
  let D' : W.left.EffectiveCartierDivisor := D.comapFiniteEtale W
  have hreg' : D'.IsAmbientRegularAlongSupport :=
    Scheme.IdealSheafData.IsAmbientRegularAlongSupport.comap_of_etale D.1 W.hom hreg
  let : ConnectedSpace D'.1.supportComplement := boundaryComplement_connectedSpace D' hreg'
  let e : ((pullback D.1.supportComplement.ι).obj W).left ≅ D'.1.supportComplement :=
    pullbackSupportComplementIso D.1 W
  let : ConnectedSpace ((pullback D.1.supportComplement.ι).obj W).left :=
    e.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  exact isConnected_of_connectedSpace_left ((pullback D.1.supportComplement.ι).obj W)

/-- The morphism on fundamental groups in Lemma 1.1 is surjective. -/
theorem boundaryComplement_fundamentalGroupHom_surjective
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ D.1.supportComplement) :
    Function.Surjective (fundamentalGroupHom D.1.supportComplement.ι point) := by
  let j : (D.1.supportComplement : Scheme) ⟶ X := D.1.supportComplement.ι
  let : Limits.PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback j) :=
    pullback_preservesLimitsOfShape_pempty j
  change Function.Surjective (autHomOfCompIso (pullback j) (pullbackFiberIso j point))
  apply ((autHomOfCompIso_surjective_tfae (fiber (point ≫ j)) (fiber point)
    (pullback j) (pullbackFiberIso j point)).out 3 1).mp
  intro W hW
  let : IsConnected W := hW
  exact boundaryComplement_pullback_isConnected D hreg W

end AlgebraicGeometry.FiniteEtale
