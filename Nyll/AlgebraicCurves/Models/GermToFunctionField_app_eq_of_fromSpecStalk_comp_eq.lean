/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sober
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.CategoryTheory.Category.Basic

/-!
# Germ To Function Field app eq of from Spec Stalk comp eq
-/

section ProofImplementation


namespace AlgebraicCurves.Models.Proofs.GermToFunctionField_app_eq_of_fromSpecStalk_comp_eq

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicCurve
namespace GlueAux

theorem comp_algebraMap_stalk_eq
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X))
    (y : Y) :
    φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField) =
      (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom := by
  have eX : CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField)) =
      X.presheaf.stalkSpecializes (genericPoint_specializes (π y)) ≫ CommRingCat.ofHom φ := rfl
  have eY : CommRingCat.ofHom ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap
    y).hom) =
      π.stalkMap y ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes y) := rfl
  have key : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y))
    X.functionField))) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) := by
    have l1 : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y))
      X.functionField))) ≫
        X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      exact (congrArg
        (fun f : X.presheaf.stalk (π y) ⟶ Y.functionField =>
          Spec.map f ≫ X.fromSpecStalk (π y)) eX).trans
        ((Spec.map_comp_assoc
          (X.presheaf.stalkSpecializes (genericPoint_specializes (π y)))
          (CommRingCat.ofHom φ) (X.fromSpecStalk (π y))).trans
          ((congrArg
            (fun f : Spec X.functionField ⟶ X => Spec.map (CommRingCat.ofHom φ) ≫ f)
            (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X)
              (genericPoint_specializes (π y)))).trans hφπ.symm))
    have l2 : Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) ≫
        X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      exact (congrArg
        (fun f : X.presheaf.stalk (π y) ⟶ Y.functionField =>
          Spec.map f ≫ X.fromSpecStalk (π y)) eY).trans
        ((Spec.map_comp_assoc (π.stalkMap y)
          (Y.presheaf.stalkSpecializes (genericPoint_specializes y))
          (X.fromSpecStalk (π y))).trans
          ((congrArg
            (fun f : Spec (Y.presheaf.stalk y) ⟶ X =>
              Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes y)) ≫ f)
            (Scheme.SpecMap_stalkMap_fromSpecStalk (f := π) (x := y))).trans
            (Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc
              (X := Y) (genericPoint_specializes y) π)))
    rw [← cancel_mono (X.fromSpecStalk (π y)), l1, l2]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

end AlgebraicCurve.GlueAux

theorem _root_.AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) [Nonempty (U : Scheme.{u})] [Nonempty ((π ⁻¹ᵁ U : Y.Opens) : Scheme.{u})] (s :
      Γ(X, U)) :
    (Y.germToFunctionField (π ⁻¹ᵁ U)).hom (π.app U s) = φ ((X.germToFunctionField U).hom s) := by
  have hη : genericPoint Y ∈ π ⁻¹ᵁ U :=
    ((genericPoint_spec Y).mem_open_set_iff (π ⁻¹ᵁ U).isOpen).mpr
      (by simpa using ‹Nonempty ((π ⁻¹ᵁ U : Y.Opens) : Scheme.{u})›)
  have hπη : π (genericPoint Y) ∈ U := hη
  have hc := AlgebraicCurve.GlueAux.comp_algebraMap_stalk_eq π φ hφπ (genericPoint Y)
  have hc' : φ.comp (X.presheaf.stalkSpecializes (genericPoint_specializes (π (genericPoint
    Y)))).hom =
      (Y.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint Y))).hom.comp
        (π.stalkMap (genericPoint Y)).hom := hc
  have e1 : X.germToFunctionField U =
      X.presheaf.germ U (π (genericPoint Y)) hπη ≫
        X.presheaf.stalkSpecializes (genericPoint_specializes (π (genericPoint Y))) :=
    (X.presheaf.germ_stalkSpecializes hπη (genericPoint_specializes _)).symm
  have e2 : (Y.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint Y))).hom =
    RingHom.id _ := by
    rw [Y.presheaf.stalkSpecializes_refl]; rfl
  have e3 : (π.stalkMap (genericPoint Y)).hom ((X.presheaf.germ U (π (genericPoint Y)) hπη).hom s) =
      (Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hπη).hom (π.app U s) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap]
  have e1' : (X.germToFunctionField U).hom s =
      (X.presheaf.stalkSpecializes (genericPoint_specializes (π (genericPoint Y)))).hom
        ((X.presheaf.germ U (π (genericPoint Y)) hπη).hom s) := by
    rw [e1]; rfl
  have hcs := congrArg (fun g => g ((X.presheaf.germ U (π (genericPoint Y)) hπη).hom s)) hc'
  simp only [RingHom.comp_apply, e2, RingHom.id_apply, e3] at hcs
  rw [e1', hcs]
end AlgebraicCurves.Models.Proofs.GermToFunctionField_app_eq_of_fromSpecStalk_comp_eq
end ProofImplementation
