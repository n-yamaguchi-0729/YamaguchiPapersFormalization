/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.DominantPreimmersionPullbackAbelian
import EtaleFundamentalGroups.GaloisCovers.ExtensionAcrossSourceIso
import EtaleFundamentalGroups.Purity.ConnectedNormalizationExtension
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Canonical normalization extensions on open-normal pullback models

The source of an open-normal pullback model is canonically the complement of
the pulled boundary.  This file transports a cover across that isomorphism,
uses the canonical function-field normalization as its extension, and then
transports the resulting pullback isomorphism back to the original model.
-/

noncomputable section


open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

namespace OpenNormalPullbackModel

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  [IsLocallyNoetherian X]
variable (I : X.IdealSheafData) [ConnectedSpace I.supportComplement]
  [Nonempty I.supportComplement]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]
variable (xi : Spec (.of Omega) ⟶ I.supportComplement)
variable (U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ I.supportComplement.ι))

/-- The cover on the pulled boundary complement obtained by transporting a
cover on the selected pullback component across the canonical source
isomorphism. -/
noncomputable def coverOnPulledSupportComplement
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U)
    (W : FiniteEtale M.sourceScheme) :
    FiniteEtale (I.comap M.targetCover.hom).supportComplement :=
  let e := M.sourceIsoPulledSupportComplementOver I xi U
  (pullback e.inv).obj W

noncomputable instance targetSchemeIsIntegral
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    IsIntegral M.targetCover.left := by
  let : IsGalois M.targetCover := M.targetIsGalois
  exact EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale
    M.targetCover

noncomputable instance targetSchemeIsNormalIntegral
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    IsNormalIntegral M.targetCover.left := by
  let : IsGalois M.targetCover := M.targetIsGalois
  exact EtaleFundamentalGroups.isNormalIntegral_left_of_isConnected_finiteEtale
    M.targetCover

noncomputable instance targetSchemeIsLocallyNoetherian
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    IsLocallyNoetherian M.targetCover.left :=
  EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale M.targetCover

-- `Opens.ι` exposes its codomain through the identity functor.  Register the
-- transported instances at that literal type to keep typeclass search opaque
-- to the implementation of scheme restrictions.
noncomputable instance targetSchemeIdIsIntegral
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    IsIntegral ((𝟭 Scheme).obj M.targetCover.left) := by
  rw [CategoryTheory.Functor.id_obj]
  exact M.targetSchemeIsIntegral I xi U

noncomputable instance targetSchemeIdIsNormalIntegral
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    IsNormalIntegral ((𝟭 Scheme).obj M.targetCover.left) := by
  simpa only [CategoryTheory.Functor.id_obj] using
    (M.targetSchemeIsNormalIntegral I xi U)

noncomputable instance targetSchemeIdIsLocallyNoetherian
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    IsLocallyNoetherian ((𝟭 Scheme).obj M.targetCover.left) := by
  rw [CategoryTheory.Functor.id_obj]
  exact M.targetSchemeIsLocallyNoetherian I xi U

noncomputable instance pulledSupportComplementConnectedSpace
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    ConnectedSpace (I.comap M.targetCover.hom).supportComplement := by
  let e := M.sourceIsoPulledSupportComplementOver I xi U
  exact e.hom.homeomorph.connectedSpace_iff.mp inferInstance

noncomputable instance pulledSupportComplementIsIntegral
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    IsIntegral (I.comap M.targetCover.hom).supportComplement := by
  let : IsIntegral M.targetCover.left := M.targetSchemeIsIntegral I xi U
  exact isIntegral_of_isOpenImmersion
    (I.comap M.targetCover.hom).supportComplement.ι

noncomputable instance pulledSupportComplementIsNormalIntegral
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    IsNormalIntegral (I.comap M.targetCover.hom).supportComplement := by
  let : IsNormalIntegral M.targetCover.left :=
    M.targetSchemeIsNormalIntegral I xi U
  infer_instance

noncomputable instance pulledSupportComplementIsLocallyNoetherian
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    IsLocallyNoetherian (I.comap M.targetCover.hom).supportComplement := by
  let : IsLocallyNoetherian M.targetCover.left :=
    M.targetSchemeIsLocallyNoetherian I xi U
  infer_instance

noncomputable instance pulledSupportComplementInclusionQuasiCompact
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    QuasiCompact (I.comap M.targetCover.hom).supportComplement.ι := by
  infer_instance

/-- Transport across the source isomorphism preserves a connected Galois
cover. -/
theorem coverOnPulledSupportComplement_isGalois
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U)
    (W : FiniteEtale M.sourceScheme) (hW : IsGalois W) :
    IsGalois (M.coverOnPulledSupportComplement I xi U W) := by
  let : IsGalois M.sourceCover := M.sourceIsGalois
  let : IsIntegral M.sourceScheme :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale
      M.sourceCover
  let : IsNormalIntegral M.sourceScheme :=
    EtaleFundamentalGroups.isNormalIntegral_left_of_isConnected_finiteEtale
      M.sourceCover
  let : IsLocallyNoetherian M.sourceScheme :=
    EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale
      M.sourceCover
  let e := M.sourceIsoPulledSupportComplementOver I xi U
  let : ConnectedSpace (I.comap M.targetCover.hom).supportComplement :=
    e.hom.homeomorph.connectedSpace_iff.mp inferInstance
  exact pullback_obj_isGalois_of_isPreimmersion_of_isDominant
    e.inv W hW

/-- Transport across the source isomorphism also preserves commutativity of
the deck group. -/
theorem coverOnPulledSupportComplement_aut_isMulCommutative
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U)
    (W : FiniteEtale M.sourceScheme) (hW : IsGalois W)
    [IsMulCommutative (Aut W)] :
    let W' := M.coverOnPulledSupportComplement I xi U W
    let hW' : IsGalois W' :=
      M.coverOnPulledSupportComplement_isGalois I xi U W hW
    letI : IsGalois W' := hW'
    IsMulCommutative (Aut W') := by
  dsimp only
  let : IsGalois M.sourceCover := M.sourceIsGalois
  let : IsIntegral M.sourceScheme :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale
      M.sourceCover
  let : IsNormalIntegral M.sourceScheme :=
    EtaleFundamentalGroups.isNormalIntegral_left_of_isConnected_finiteEtale
      M.sourceCover
  let : IsLocallyNoetherian M.sourceScheme :=
    EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale
      M.sourceCover
  let e := M.sourceIsoPulledSupportComplementOver I xi U
  let : ConnectedSpace (I.comap M.targetCover.hom).supportComplement :=
    e.hom.homeomorph.connectedSpace_iff.mp inferInstance
  exact pullback_obj_aut_isMulCommutative_of_isPreimmersion_of_isDominant
    e.inv W hW

/-- Finite etaleness of the canonical normalization of the transported cover
produces an actual extension over the target cover and the required pullback
isomorphism over the original open-normal model. -/
noncomputable def extensionOfCanonicalNormalization
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U)
    (W : FiniteEtale M.sourceScheme) (hW : IsGalois W)
    (hEtale :
      let W' := M.coverOnPulledSupportComplement I xi U W
      let hW' : IsGalois W' :=
        M.coverOnPulledSupportComplement_isGalois I xi U W hW
      letI : IsGalois W' := hW'
      let j := (I.comap M.targetCover.hom).supportComplement.ι
      IsFiniteEtale (connectedCoverGenericComposite W' ≫ j).fromNormalization) :
    Σ Z : FiniteEtale M.targetScheme, (pullback M.hom).obj Z ≅ W := by
  letI : IsGalois M.targetCover := M.targetIsGalois
  letI : IsIntegral M.targetCover.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale
      M.targetCover
  letI : IsNormalIntegral M.targetCover.left :=
    EtaleFundamentalGroups.isNormalIntegral_left_of_isConnected_finiteEtale
      M.targetCover
  letI : IsLocallyNoetherian M.targetCover.left :=
    EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale
      M.targetCover
  let e := M.sourceIsoPulledSupportComplementOver I xi U
  letI : ConnectedSpace (I.comap M.targetCover.hom).supportComplement :=
    e.hom.homeomorph.connectedSpace_iff.mp inferInstance
  letI : IsIntegral (I.comap M.targetCover.hom).supportComplement :=
    isIntegral_of_isOpenImmersion
      (I.comap M.targetCover.hom).supportComplement.ι
  let W' := M.coverOnPulledSupportComplement I xi U W
  let hW' : IsGalois W' :=
    M.coverOnPulledSupportComplement_isGalois I xi U W hW
  letI : IsGalois W' := hW'
  let j := (I.comap M.targetCover.hom).supportComplement.ι
  let extension := connectedCoverExtensionOfNormalization W' j hEtale
  exact extensionOfSourceIso e j M.hom
    (M.sourceIsoPulledSupportComplementOver_hom_comp_ι I xi U)
    W extension

end OpenNormalPullbackModel

end AlgebraicGeometry.FiniteEtale
