/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalPullbackModel
import Nyll.SchemeTheory.Divisors.LocalComplement

/-!
# Open-normal pullback models over open immersions

For a nonempty open immersion into a normal locally Noetherian integral
scheme, the pullback of a connected finite-etale cover is connected.  Hence
the connected component occurring in an open-normal pullback model is the
whole pullback.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

namespace OpenNormalPullbackModel

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]
variable {f : X ⟶ Y} {xi : Spec (.of Omega) ⟶ X}
variable {U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ f)}

/-- Over a nonempty open immersion into a normal locally Noetherian integral
scheme, the selected Galois component is the entire pulled-back cover. -/
theorem inclusion_isIso_of_isOpenImmersion
    [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    [IsOpenImmersion f] [Nonempty X]
    (M : OpenNormalPullbackModel f xi U) : IsIso M.inclusion := by
  let : IsGalois M.targetCover := M.targetIsGalois
  let : IsConnected ((pullback f).obj M.targetCover) :=
    EtaleFundamentalGroups.pullback_obj_isConnected_of_isOpenImmersion
      f M.targetCover
  let : IsGalois M.sourceCover := M.sourceIsGalois
  let : Mono M.inclusion := M.inclusionMono
  exact IsConnected.noTrivialComponent M.sourceCover M.inclusion
    (not_initial_of_inhabited (fiber xi) M.sourcePoint)

/-- The scheme underlying the selected component is canonically isomorphic
to the scheme underlying the entire pulled-back cover. -/
noncomputable def sourceIsoPullback_of_isOpenImmersion
    [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    [IsOpenImmersion f] [Nonempty X]
    (M : OpenNormalPullbackModel f xi U) :
    M.sourceScheme ≅ ((pullback f).obj M.targetCover).left := by
  letI : IsIso M.inclusion := M.inclusion_isIso_of_isOpenImmersion
  letI hinclusionHom : IsIso M.inclusion.hom :=
    (FiniteEtale.forget X).map_isIso M.inclusion
  letI hinclusionLeft : IsIso M.inclusion.left :=
    @Functor.map_isIso _ _ _ _ _ _
      (CategoryTheory.Over.forget X) M.inclusion.hom hinclusionHom
  exact asIso M.inclusion.left

end OpenNormalPullbackModel

/-- Pulling a finite-etale cover back to the support complement of an ideal
sheaf gives the support complement of the pulled-back ideal sheaf. -/
noncomputable def pullbackSupportComplementIso
    {Y : Scheme.{u}} (I : Y.IdealSheafData) (A : FiniteEtale Y) :
    ((pullback I.supportComplement.ι).obj A).left ≅
      (I.comap A.hom).supportComplement :=
  pullbackRestrictIsoRestrict A.hom I.supportComplement ≪≫
    A.left.isoOfEq (I.supportComplement_comap A.hom).symm

namespace OpenNormalPullbackModel

variable {Y : Scheme.{u}} [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- For a boundary complement, the source scheme of an open-normal model is
the support complement of the boundary pulled back to its target cover. -/
noncomputable def sourceIsoPulledSupportComplement
    [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) [ConnectedSpace I.supportComplement]
    [Nonempty I.supportComplement]
    (xi : Spec (.of Omega) ⟶ I.supportComplement)
    (U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ I.supportComplement.ι))
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    M.sourceScheme ≅ (I.comap M.targetCover.hom).supportComplement :=
  M.sourceIsoPullback_of_isOpenImmersion ≪≫
    pullbackSupportComplementIso I M.targetCover

end OpenNormalPullbackModel

end AlgebraicGeometry.FiniteEtale
