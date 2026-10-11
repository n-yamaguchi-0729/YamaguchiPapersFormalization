/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Flat.Basic

/-!
# Injective-valued duals of flat modules

Tensoring an injection with a flat module is injective. An extension into
an injective module along that tensor map can therefore be curried into
an extension with values in the linear dual. This supplies the injective
terms when a flat local-cohomology complex is dualized.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open scoped TensorProduct

variable {R : Type u} [CommRing R]

/-- The linear dual of a flat module with values in an injective module
is injective. The extension is obtained by tensoring, extending, and
currying; no injectivity assumption on the dual is needed. -/
theorem injective_linearMap_of_flat
    (F E : Type u) [AddCommGroup F] [Module R F] [Module.Flat R F]
    [AddCommGroup E] [Module R E] [Module.Injective R E] :
    Module.Injective R (F →ₗ[R] E) where
  out X Y _ _ _ _ f hf g := by
    have hft : Function.Injective (f.rTensor F) :=
      Module.Flat.rTensor_preserves_injective_linearMap f hf
    obtain ⟨h, hh⟩ := Module.Injective.out (f.rTensor F) hft (TensorProduct.lift g)
    refine ⟨TensorProduct.curry h, ?_⟩
    intro x
    ext z
    simpa only [TensorProduct.curry_apply, LinearMap.rTensor_tmul,
      TensorProduct.lift.tmul] using hh (x ⊗ₜ[R] z)

end EtaleFundamentalGroups.Purity
