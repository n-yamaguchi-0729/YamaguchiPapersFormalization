/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.DominantPreimmersionPullback
import EtaleFundamentalGroups.GeometricFiber.AlgebraicClosure
import EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import SchemeTheory.Normalization.FiniteSeparable

/-!
# The generic absolute Galois map of a normal integral scheme

The geometric generic point determines a continuous map from the absolute
Galois group of the function field to the étale fundamental group. For a
normal integral scheme this map is surjective, because dominant
preimmersions preserve connected finite étale covers.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A dominant quasi-compact preimmersion into a normal integral scheme
induces a surjection on fundamental groups at each geometric point. -/
theorem fundamentalGroupHom_surjective_of_isPreimmersion_of_isDominant
    {U X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [ConnectedSpace U]
    (j : U ⟶ X) [IsPreimmersion j] [IsDominant j] [QuasiCompact j]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ U) :
    Function.Surjective (fundamentalGroupHom j xi) := by
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback j) :=
    pullback_preservesLimitsOfShape_pempty j
  change Function.Surjective
    (autHomOfCompIso (pullback j) (pullbackFiberIso j xi))
  apply ((autHomOfCompIso_surjective_tfae
    (fiber (xi ≫ j)) (fiber xi) (pullback j)
    (pullbackFiberIso j xi)).out 3 1).mp
  intro W hW
  let : IsConnected W := hW
  exact pullback_obj_isConnected_of_isPreimmersion_of_isDominant j W

/-- The canonical absolute Galois map at the geometric generic point.
The field fundamental group is identified using the separable closure
inside the algebraic closure. -/
def genericAbsoluteGaloisHom (X : Scheme.{u}) [IsIntegral X] :
    (SeparableClosure X.functionField ≃ₐ[X.functionField]
      SeparableClosure X.functionField) →ₜ*
        π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)) :=
  (fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
    (Spec.map (CommRingCat.ofHom
      (algebraMap X.functionField (AlgebraicClosure X.functionField))))).comp
        (ContinuousMonoidHom.toContinuousMonoidHom
          (absoluteGaloisEquivFundamentalGroup X.functionField))

/-- The absolute Galois group of the function field surjects onto the
fundamental group of a normal integral scheme. -/
theorem genericAbsoluteGaloisHom_surjective
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X] :
    Function.Surjective (genericAbsoluteGaloisHom X) := by
  let j := X.fromSpecStalk (genericPoint X)
  let : QuasiCompact j :=
    { isCompact_preimage := fun U _ _ ↦ (Set.toFinite (j ⁻¹' U)).isCompact }
  let : IsDominant j := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro x
    apply (genericPoint_specializes x).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint (CommRingCat.of X.functionField),
      Scheme.fromSpecStalk_closedPoint (X := X) (x := genericPoint X)⟩
  have hj : Function.Surjective
      (fundamentalGroupHom j
        (Spec.map (CommRingCat.ofHom
          (algebraMap X.functionField (AlgebraicClosure X.functionField))))) :=
    fundamentalGroupHom_surjective_of_isPreimmersion_of_isDominant j _
  exact hj.comp (absoluteGaloisEquivFundamentalGroup X.functionField).surjective

end AlgebraicGeometry.FiniteEtale
