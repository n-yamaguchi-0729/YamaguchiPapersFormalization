/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Geometry.Schemes.FunctionFieldConstantExtension
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase

/-!
# Scalar compatibility of the actual constant-extension function-field map

The germ comparison of the geometric projection forces its action on the
original constants. This supplies the scalar tower used by divisor conorm
and Weil evaluation without assuming a comparison of coefficient maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry

/-- The actual function-field map characterized by germs sends original
constants through the specified extension of the ground field. -/
theorem functionField_constantExtension_map_constants
    {K : Type} [Field K] (K' : Type) [Field K'] [Algebra K K']
    {X : Scheme} [IsIntegral X] (c : X ⟶ Spec (.of K))
    [IsIntegral (pullback c (specMap K K'))]
    (φ : X.functionField →+* (pullback c (specMap K K')).functionField)
    (hsq : ∀ (U : X.Opens) [Nonempty U]
      [Nonempty ((pullback.fst c (specMap K K')) ⁻¹ᵁ U)] (s : Γ(X, U)),
      (pullback c (specMap K K')).germToFunctionField
        ((pullback.fst c (specMap K K')) ⁻¹ᵁ U)
        (((pullback.fst c (specMap K K')).app U).hom s) =
          φ (X.germToFunctionField U s))
    (a : K) :
    φ (baseToFunctionField c a) =
      baseToFunctionField (pullback.snd c (specMap K K')) (algebraMap K K' a) := by
  let Y := pullback c (specMap K K')
  let p := pullback.fst c (specMap K K')
  let b := pullback.snd c (specMap K K')
  have hsection :
      p.appTop.hom (c.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom a)) =
        b.appTop.hom ((specMap K K').appTop.hom
          ((Scheme.ΓSpecIso (.of K)).inv.hom a)) := by
    change (c.appTop ≫ p.appTop).hom _ =
      ((specMap K K').appTop ≫ b.appTop).hom _
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, pullback.condition]
  have hscalar :
      (specMap K K').appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom a) =
        (Scheme.ΓSpecIso (.of K')).inv.hom (algebraMap K K' a) := by
    have h := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K K')))
    exact h.symm
  have hX : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have hY : Nonempty (p ⁻¹ᵁ (⊤ : X.Opens)) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hYtop : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hgerm := hsq ⊤ (c.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom a))
  change (Y.germToFunctionField ⊤).hom
      (p.appTop.hom (c.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom a))) =
        φ (baseToFunctionField c a) at hgerm
  rw [← hgerm, hsection, hscalar]
  rfl

end AlgebraicGeometry
