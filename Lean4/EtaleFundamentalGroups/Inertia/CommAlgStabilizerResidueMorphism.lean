/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueEpi
import SchemeTheory.RingTheory.Ramification.NativeResidueAction
import SchemeTheory.CategoryTheory.CommAlgRingMap
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Residue morphisms for intrinsic stabilizers

Proves coefficient preservation by intrinsic algebra automorphisms and constructs the resulting
native quotient-residue morphism.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

/-- The intrinsic algebra automorphisms preserve the stored coefficient map. -/
theorem commAlgAutomorphism_comp_coefficient
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (σ : B ≃ₐ[A] B) :
    (MulSemiringAction.toRingHom (B ≃ₐ[A] B) B σ).comp
        (commAlgCoefficientMap B) = commAlgCoefficientMap B := by
  change σ.toRingHom.comp (algebraMap A B) = algebraMap A B
  exact σ.toAlgHom.comp_algebraMap

/-- The same native quotient-residue morphism for the actual intrinsic
normalization automorphisms, with coefficient preservation proved above. -/
def commAlgStabilizerResidueMorphism
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (Q : Ideal B) :
    GrpCat.Hom (nativeResidueStabilizer B (B ≃ₐ[A] B) Q)
      (nativeAlgebraResidueAutomorphisms B Q) :=
  nativeAlgebraResidueMorphism B (B ≃ₐ[A] B) Q
    (commAlgAutomorphism_comp_coefficient A B)

end EtaleFundamentalGroups.Inertia
