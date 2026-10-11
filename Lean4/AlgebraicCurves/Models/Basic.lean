/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CurveModel.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import AlgebraicCurves.Divisors.ClassGroup

/-!
Geometric models of function fields of curves.
A model identifies closed points with places and stalks with their valuation subrings.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicCurve

/-- The base-field homomorphism into the function field induced by the structure morphism. -/
def baseToFunctionField {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) : K →+* C.functionField :=
  (C.presheaf.germ ⊤ (genericPoint C) trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

/-- A proper smooth integral curve model of a field extension, with its place correspondence. -/
structure CurveModel (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] where
  /-- The underlying scheme of the curve model. -/
  C : Scheme.{u}
  /-- The structure morphism to the spectrum of the base field. -/
  toBase : C ⟶ Spec (CommRingCat.of K)
  /-- The underlying scheme is integral. -/
  [isIntegral : IsIntegral C]
  /-- The structure morphism is proper. -/
  [isProper : IsProper toBase]
  /-- The structure morphism is smooth of relative dimension one. -/
  [smooth : SmoothOfRelativeDimension 1 toBase]
  /-- The specified ring equivalence with the model function field. -/
  ffEquiv : L ≃+* C.functionField
  /-- The function-field equivalence respects the specified base-field homomorphisms. -/
  ffEquiv_algebraMap : ∀ a : K, ffEquiv (algebraMap K L a) = baseToFunctionField toBase a
  /-- The place associated with each closed point of the model. -/
  placeOfPoint : closedPoints C → Place K L
  /-- Closed points correspond bijectively to places. -/
  placeOfPoint_bijective : Function.Bijective placeOfPoint
  /-- The stalk image transported to the given field is the corresponding valuation subring. -/
  range_stalk_eq : ∀ x : closedPoints C,
    ((ffEquiv.symm : C.functionField ≃+* L).toRingHom.comp
        (algebraMap (C.presheaf.stalk x.1) C.functionField)).range =
      (placeOfPoint x).toValuationSubring.toSubring
  /-- Every finite subset of the model lies in an affine open. -/
  finset_subset_affineOpen : ∀ F : Finset C, ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U

attribute [instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- The base-field algebra structure on the model function field. -/
abbrev functionFieldAlgebra (M : CurveModel K L) : Algebra K M.C.functionField :=
  (baseToFunctionField M.toBase).toAlgebra

/-- The specified function-field equivalence regarded as a base-field algebra equivalence. -/
def ffAlgEquiv (M : CurveModel K L) :
    letI := M.functionFieldAlgebra
    L ≃ₐ[K] M.C.functionField :=
  letI := M.functionFieldAlgebra
  AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap

theorem ffAlgEquiv_apply (M : CurveModel K L) (f : L) : M.ffAlgEquiv f = M.ffEquiv f := rfl

/-- The equivalence between closed points of the model and places of the given field. -/
def placeEquiv (M : CurveModel K L) : closedPoints M.C ≃ Place K L :=
  Equiv.ofBijective M.placeOfPoint M.placeOfPoint_bijective

theorem placeEquiv_apply (M : CurveModel K L) (x : closedPoints M.C) :
    M.placeEquiv x = M.placeOfPoint x := rfl

/-- Identify base-field points with places over an algebraically closed base field. -/
def pointEquivPlace [IsAlgClosed K] (M : CurveModel K L) :
    {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} ≃ Place K L :=
  (pointEquivClosedPoint M.toBase).trans M.placeEquiv

theorem pointEquivPlace_apply [IsAlgClosed K] (M : CurveModel K L)
    (p : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    M.pointEquivPlace p = M.placeOfPoint (pointEquivClosedPoint M.toBase p) := rfl

end CurveModel

end AlgebraicCurve

end
