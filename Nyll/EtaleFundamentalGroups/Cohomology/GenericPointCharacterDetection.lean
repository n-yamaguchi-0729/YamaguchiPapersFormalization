/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison

/-!
# Detecting actual finite H¹ classes at a separably closed generic point

The closure is arbitrary. This allows a geometric comparison made in the
chosen constant-field extension to determine the actual global H¹ class.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

/-- Every automorphism of the geometric generic fibre of a normal integral
scheme comes from a field automorphism of its chosen separable closure. -/
theorem genericFieldAction_surjective
    (X : Scheme) [IsIntegral X] [IsNormalIntegral X]
    (Ω : Type) [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] :
    Function.Surjective (fun σ : Ω ≃ₐ[X.functionField] Ω =>
      fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
        (toAut (fib X.functionField Ω) (Ω ≃ₐ[X.functionField] Ω) σ)) := by
  let j := X.fromSpecStalk (genericPoint X)
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
  have : QuasiCompact j :=
    { isCompact_preimage := fun U _ _ => (Set.toFinite (j ⁻¹' U)).isCompact }
  have : IsDominant j := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro x
    apply (genericPoint_specializes x).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint (CommRingCat.of X.functionField),
      Scheme.fromSpecStalk_closedPoint (X := X) (x := genericPoint X)⟩
  have hj := fundamentalGroupHom_surjective_of_isPreimmersion_of_isDominant j η
  have ha : Function.Surjective
      (toAut (fib X.functionField Ω) (Ω ≃ₐ[X.functionField] Ω)) := by
    intro g
    obtain ⟨σ, hσ⟩ :=
      (toAutHomeo (fib X.functionField Ω) (Ω ≃ₐ[X.functionField] Ω)).surjective g
    exact ⟨σ, (toAutHomeo_apply _ σ).symm.trans hσ⟩
  exact hj.comp ha

end AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.Cohomology

/-- Equality of actual finite H¹ classes is detected by their characters
on field automorphisms at any chosen separably closed generic point. -/
theorem finiteH1_ext_genericFieldAction
    (X : Scheme) [IsIntegral X] [IsNormalIntegral X]
    (Ω : Type) [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    (A : AddCommGrpCat.{0}) [Finite A]
    (a b : Sheaf.H.{0} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    (∀ σ : Ω ≃ₐ[X.functionField] Ω,
      (finiteH1CharacterEquiv A ξ a).toMul
          (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)) =
      (finiteH1CharacterEquiv A ξ b).toMul
          (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ))) ->
      a = b := by
  intro η ξ htop hdiscrete h
  apply (finiteH1CharacterEquiv A ξ).injective
  apply ContinuousMonoidHom.ext
  intro g
  obtain ⟨σ, rfl⟩ := FiniteEtale.genericFieldAction_surjective X Ω g
  exact h σ

end EtaleFundamentalGroups.Cohomology
