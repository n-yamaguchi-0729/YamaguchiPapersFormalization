/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality

/-! # Scalar compatibility of actual function-field pullback -/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicCurve

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Actual function-field pullback commutes with the actual structure maps
to the ground field. -/
theorem functionFieldMap_baseToFunctionField
    (c : X ⟶ Spec (.of K)) (f : Y ⟶ X) (hf : DenseRange f) (a : K) :
    f.functionFieldMap hf (baseToFunctionField c a) =
      baseToFunctionField (f ≫ c) a := by
  have : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩
  have : Nonempty (⊤ : Y.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Y), trivial⟩⟩
  have h := DFunLike.congr_fun (f.functionFieldMap_comp_germToFunctionField_top hf)
    (c.appTop ((Scheme.ΓSpecIso (.of K)).inv a))
  change f.functionFieldMap hf (baseToFunctionField c a) =
    Y.germToFunctionField ⊤ (f.appTop (c.appTop ((Scheme.ΓSpecIso (.of K)).inv a))) at h
  change f.functionFieldMap hf (baseToFunctionField c a) =
    Y.germToFunctionField ⊤ ((f ≫ c).appTop ((Scheme.ΓSpecIso (.of K)).inv a))
  rw [Scheme.Hom.comp_appTop]
  exact h

/-- The literal map of function fields as a homomorphism over the actual
ground-field algebra structures. -/
def functionFieldAlgHomOver
    (c : X ⟶ Spec (.of K)) (f : Y ⟶ X) (hf : DenseRange f) :
    let : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
    let : Algebra K Y.functionField := (baseToFunctionField (f ≫ c)).toAlgebra
    X.functionField →ₐ[K] Y.functionField := by
  let : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
  let : Algebra K Y.functionField := (baseToFunctionField (f ≫ c)).toAlgebra
  exact
    { f.functionFieldMap hf with
      commutes' := functionFieldMap_baseToFunctionField c f hf }

end AlgebraicGeometry.Scheme.Hom
