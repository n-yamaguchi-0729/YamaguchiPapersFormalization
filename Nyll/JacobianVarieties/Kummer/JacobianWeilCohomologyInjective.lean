/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.WeilPairing.CharZeroNondegeneracy
import Nyll.JacobianVarieties.WeilPairing.Divisorial
import Nyll.JacobianVarieties.Autoduality.Cohomology
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationMonodromy
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Injectivity of actual Jacobian Weil cohomology classes

The evaluation formula supplied by `exists_jacobian_weil_cohomology`
identifies the character with the actual multiplication-cover action.
Surjectivity of that action and geometrically proved nondegeneracy of the
divisorial pairing imply injectivity. No faithfulness or nondegeneracy
assumption is added to the cohomological construction.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open EtaleFundamentalGroups.Cohomology

namespace JacobianVarieties.Kummer

/-- The actual Weil cohomology classes are injective, using the evaluation
formula already supplied by their construction. -/
theorem jacobian_weil_cohomology_injective
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {J : Scheme} {b : J ⟶ Spec (.of K)}
    [Smooth b] [IsProper b] [GeometricallyConnected b]
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative) (n : ℕ+)
    (τ : Pic0.torsion K F (n : ℕ) ≃+ ProCGroups.torsionLevel (G.AlgPoints hc K) n)
    (w : DivisorialWeilPairingData K F (n : ℕ)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    let : ConnectedSpace J := GeometricallyConnected.connectedSpace b b.isOpenMap
    ∀ ν : Pic0.torsion K F (n : ℕ) →+
        Sheaf.H.{0} ((constantSheaf J.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1,
      (∀ (x : Pic0.torsion K F (n : ℕ))
        (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)),
        ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 (ν x)).toMul g :
          rootsOfUnity (n : ℕ) K).val.val =
            w.pair x (τ.symm (G.multiplicationMonodromy hc n g))) →
      Function.Injective ν := by
  intro htop hdiscrete A hAtop hAdiscrete hconnected ν hν x y hxy
  apply w.toHom_injective_charZero hfg
  change w.toChar x = w.toChar y
  ext z
  obtain ⟨g, hg⟩ := G.multiplicationMonodromy_surjective hc n (τ z)
  have h := congrArg (fun a =>
    ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 a).toMul g :
      rootsOfUnity (n : ℕ) K).val.val) hxy
  rw [hν x g, hν y g, hg, τ.symm_apply_apply] at h
  exact h

end JacobianVarieties.Kummer
