/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Arithmetic generic fibers after characteristic-zero field extension

Every point of a characteristic-zero field maps to the generic point of
`Spec ℤ`. The fiber base-change square therefore transports geometric
integrality of the generic fiber to every such field extension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace EtaleFundamentalGroups

/-- A characteristic-zero field point of the integer scheme is its generic
point. -/
theorem specMap_int_field_eq_genericPoint
    (K : Type) [Field K] [CharZero K] (x : Spec (CommRingCat.of K)) :
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) x =
      genericPoint (Spec (CommRingCat.of ℤ)) := by
  have hx : x = (⊥ : PrimeSpectrum K) := Subsingleton.elim _ _
  change PrimeSpectrum.comap (algebraMap ℤ K) x = _
  rw [hx, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective (algebraMap ℤ K) Int.cast_injective

/-- Geometric integrality of the arithmetic generic fiber gives geometric
integrality after every characteristic-zero field extension. -/
theorem geometricallyIntegral_pullback_of_arithmetic_genericFiber
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ))
    [GeometricallyIntegral
      (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of ℤ))))]
    (K : Type) [Field K] [CharZero K] :
    GeometricallyIntegral
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) := by
  let g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ K))
  apply (GeometricallyIntegral.iff_geometricallyIntegral_fiber (pullback.snd f g)).mpr
  intro y
  have hgi : GeometricallyIntegral (f.fiberToSpecResidueField (g y)) := by
    rw [specMap_int_field_eq_genericPoint K y]
    infer_instance
  exact MorphismProperty.of_isPullback
    (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f g) y) hgi

end EtaleFundamentalGroups
