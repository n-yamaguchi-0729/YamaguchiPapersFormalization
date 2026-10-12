/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.UnpointedExistence
import Nyll.JacobianVarieties.Picard.UnpointedGroup
import Nyll.JacobianVarieties.Picard.UnpointedDimension
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIrreducible_geometricallyConnected
import Nyll.AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_smooth_of_geometricallyConnected

/-!
# A Jacobian over an arbitrary field without a rational basepoint

A single effective descent presentation is chosen from the proved existence theorem.
Its carrier and structure map are retained by all public constructions. The relative
group law is constructed from tensor product, and its dimension is the geometric
genus of the original curve.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

noncomputable section

namespace JacobianVarieties.Picard.Unpointed

variable (K : Type u) [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))

/-- The actual finite-extension presentation retained by the Jacobian construction.
All of these data are supplied by the proved existence theorem below. -/
structure Presentation where
  /-- A finite extension on which the curve has a section. -/
  extension : Type u
  /-- The field structure of the chosen extension. -/
  extensionField : Field extension
  /-- The specified ground-field algebra structure. -/
  extensionAlgebra : Algebra K extension
  /-- Finiteness of the actual extension. -/
  extensionFinite : Module.Finite K extension
  /-- The section constructed after extending the ground field. -/
  localSection : SchemeHomOver (𝟙 (Spec (CommRingCat.of extension))) (baseChange K c extension)
  /-- The actual pointed Picard representative after extension. -/
  localPicard : RelativePic0Designation extension (baseChange K c extension)
  /-- Its universal line-bundle classification. -/
  localRepresentation : RepresentsRelSubPic (baseChange K c extension) localSection
    (algEquivZeroCut (baseChange K c extension) localSection) localPicard
  /-- The effective descent carrier over the ground field. -/
  carrier : Scheme.{u}
  /-- Its structure morphism. -/
  toBase : carrier ⟶ Spec (CommRingCat.of K)
  /-- Smoothness supplied by faithfully flat descent. -/
  smooth : Smooth toBase
  /-- Properness supplied by faithfully flat descent. -/
  proper : IsProper toBase
  /-- Geometric connectedness supplied by faithfully flat descent. -/
  geometricallyConnected : GeometricallyConnected toBase
  /-- The effective-descent comparison with the local Picard representative. -/
  comparison : pullback toBase (specMap K extension) ≅ localPicard.P
  /-- The comparison lies over the extension field. -/
  comparison_over : comparison.hom ≫ localPicard.toBase = pullback.snd toBase (specMap K extension)
  /-- The actual canonical descent action is respected by the comparison. -/
  comparison_action :
    DescentAction.eRel (specMap K extension) localPicard.toBase toBase comparison comparison_over ≫
        (descentAction c extension localSection localRepresentation).act =
      (DescentAction.canonical (specMap K extension) toBase).act ≫ comparison.hom

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

local instance curveGeometricallyIntegral : GeometricallyIntegral c := by
  have _ : GeometricallyConnected c := GeometricallyIrreducible.geometricallyConnected c
  exact geometricallyIntegral_of_smooth_of_geometricallyConnected c

/-- Construct the entire presentation using a closed point and effective descent. -/
theorem nonempty_presentation : Nonempty (Presentation K c) := by
  obtain ⟨L, hL, a, hf, ε, D, h, P, p, hs, hp, hg, e, he, hc⟩ :=
    exists_smooth_proper_picardDescent_of_field K c
  exact ⟨⟨L, hL, a, hf, ε, D, h, P, p, hs, hp, hg, e, he, hc⟩⟩

/-- One fixed effective-descent presentation; all later definitions share this value. -/
def presentation : Presentation K c := Classical.choice (nonempty_presentation K c)

/-- The Jacobian scheme over the original field, with no rational point required. -/
def Jacobian : Scheme.{u} := (presentation K c).carrier

/-- The structure morphism of the same chosen Jacobian. -/
def toBase : Jacobian K c ⟶ Spec (CommRingCat.of K) := (presentation K c).toBase

/-- The tensor-product relative group law on the chosen Jacobian. -/
def groupLaw : RelativeGroupLaw K (toBase K c) := by
  let M : Presentation K c := presentation K c
  let _ : Field M.extension := M.extensionField
  let _ : Algebra K M.extension := M.extensionAlgebra
  exact groupLawOfPicardDescent c M.extension M.localSection M.localRepresentation
    M.toBase M.comparison M.comparison_over M.comparison_action

theorem groupLaw_commutative : (groupLaw K c).IsCommutative := by
  intro T t x y
  let M : Presentation K c := presentation K c
  let _ : Field M.extension := M.extensionField
  let _ : Algebra K M.extension := M.extensionAlgebra
  exact groupLawOfPicardDescent_commutative c M.extension M.localSection M.localRepresentation
    M.toBase M.comparison M.comparison_over M.comparison_action (T := T) t x y

theorem smooth : Smooth (toBase K c) := (presentation K c).smooth

theorem proper : IsProper (toBase K c) := (presentation K c).proper

theorem geometricallyConnected : GeometricallyConnected (toBase K c) :=
  (presentation K c).geometricallyConnected

/-- Smooth relative dimension and geometric integrality concern the same chosen carrier. -/
theorem dimension_and_geometricallyIntegral :
    SmoothOfRelativeDimension (geometricGenus K c) (toBase K c) ∧
      GeometricallyIntegral (toBase K c) := by
  let M : Presentation K c := presentation K c
  let _ : Field M.extension := M.extensionField
  let _ : Algebra K M.extension := M.extensionAlgebra
  have _ : Module.Finite K M.extension := M.extensionFinite
  have _ : Smooth M.toBase := M.smooth
  have _ : IsProper M.toBase := M.proper
  have _ : GeometricallyConnected M.toBase := M.geometricallyConnected
  exact smoothOfRelativeDimension_geometricGenus_of_picardDescent K c M.extension
    M.localSection M.localRepresentation M.toBase M.comparison M.comparison_over

theorem smoothOfRelativeDimension :
    SmoothOfRelativeDimension (geometricGenus K c) (toBase K c) :=
  (dimension_and_geometricallyIntegral K c).1

theorem geometricallyIntegral : GeometricallyIntegral (toBase K c) :=
  (dimension_and_geometricallyIntegral K c).2

/-- The constructed Jacobian is an abelian variety over the original arbitrary field. -/
theorem abelianSchemePropertyBundle : AbelianSchemePropertyBundle K (toBase K c) := by
  have _ : GeometricallyConnected (toBase K c) := geometricallyConnected K c
  exact
    { smooth := smooth K c
      proper := proper K c
      connectedFibres := fun x => (toBase K c).isConnected_preimage_singleton x
      hasGroupLaw := ⟨groupLaw K c⟩ }

end JacobianVarieties.Picard.Unpointed
