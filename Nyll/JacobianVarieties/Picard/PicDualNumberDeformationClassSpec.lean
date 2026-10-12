/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Quotient.Defs
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber
import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverH1BaseChange
import Nyll.SchemeTheory.Modules.TensorSections

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints

/-!
# Cech classes of dual-number deformations

The overlap unit and compatibility condition specify the Cech class of a rigidified deformation.
-/

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry.RelPicard

section Thickening

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))

/-- The morphism of base changed covers induced by the inclusion into dual numbers. -/
abbrev dualNumberThickening :
    HomOver (IsScalarTower.toAlgHom R A (DualNumber A)).toRingHom
      (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A))) :=
  HomOver.stage 𝒱 c (IsScalarTower.toAlgHom R A (DualNumber A))

/-- The overlap unit represented by one plus epsilon times the pulled back section. -/
def oneAddEpsMul (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 :=
  1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map01 f

end Thickening

section Spec

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
variable (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

/-- First Cech cohomology of the structure sheaf on the base changed cover. -/
abbrev H1StructureSheaf : Type u :=
  ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1

/-- Compatibility of a rigidified dual-number deformation with its Cech overlap class. -/
def IsDeformationClassMap (δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱) : Prop :=
  ∀ (M : RigKerDualNumber.Carrier c ε A)
    (e₀ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U0))
    (e₁ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U1))
    (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01),
    Scheme.Modules.IsFrameOn e₀ (𝒱.pullback c (DualNumber A)).U0 →
    Scheme.Modules.IsFrameOn e₁ (𝒱.pullback c (DualNumber A)).U1 →
    M.1.L.presheaf.map (homOfLE inf_le_right).op e₁ =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
              (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1)
          from oneAddEpsMul A 𝒱 c f) •
        M.1.L.presheaf.map (homOfLE inf_le_left).op e₀ →
    δ (Quotient.mk _ M) = Submodule.Quotient.mk f

end Spec

end AlgebraicGeometry.RelPicard

end
