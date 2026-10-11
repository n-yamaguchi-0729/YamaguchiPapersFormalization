/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.Boundary
import Nyll.Yamaguchi26SolvableCoverings.Theorem1Dot1BoundaryQuotient
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot5PerfectKernel
import Nyll.Yamaguchi26SolvableCoverings.Representations.AdicPerfect
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot2BoundaryCondition
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Corollary 2.6: extending representations from their reductions

Under condition `(†)`, a continuous representation of the complement's fundamental
group over a complete Noetherian local ring with finite residue field factors through
the ambient fundamental group if and only if its residue representation does. The
factorization, when it exists, is unique.

The coefficient ring carries its maximal-ideal-adic topology and its residue field
the discrete topology. Both factorizations are continuous. The proof uses the
perfectness of the actual boundary kernel and commutator calculations in the
congruence filtration, followed by the universal property of a surjective homomorphism.

Source: [Yamaguchi, arXiv:2610.02948v1](https://arxiv.org/abs/2610.02948v1), Corollary 2.6.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale

namespace Yamaguchi26SolvableCoverings

/-- 系 2.6：完備 Noether 局所環に値を持つ連続表現が
`X` の基本群を経由することと、その剰余表現が連続的に経由することは同値であり、
元の表現の延長は存在すれば一意である。 -/
theorem residual_extension_2_6
    {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hD : BoundaryCondition D)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (point : Spec (CommRingCat.of Ω) ⟶ D.1.supportComplement)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [TopologicalSpace A] (hAdic : IsAdic (IsLocalRing.maximalIdeal A))
    [IsTopologicalRing A]
    [Finite (IsLocalRing.ResidueField A)]
    (p : ℕ) (_hp : p.Prime) [CharP (IsLocalRing.ResidueField A) p]
    (n : ℕ) (_hn : 1 ≤ n)
    (ρ : π₁ᵉᵗ(point) →ₜ* Matrix.GeneralLinearGroup (Fin n) A) :
    letI : TopologicalSpace (IsLocalRing.ResidueField A) := ⊥
    let f := fundamentalGroupHom D.1.supportComplement.ι point
    let ρbar : π₁ᵉᵗ(point) →* Matrix.GeneralLinearGroup (Fin n)
        (IsLocalRing.ResidueField A) :=
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue A)).comp ρ.toMonoidHom
    ((∃ τ : π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) →ₜ*
          Matrix.GeneralLinearGroup (Fin n) A,
        τ.comp f = ρ) ↔
      (∃ τbar : π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) →ₜ*
          Matrix.GeneralLinearGroup (Fin n) (IsLocalRing.ResidueField A),
        τbar.toMonoidHom.comp f.toMonoidHom = ρbar)) ∧
      ((∃ τ : π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) →ₜ*
          Matrix.GeneralLinearGroup (Fin n) A,
        τ.comp f = ρ) →
        ∃! τ : π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) →ₜ*
          Matrix.GeneralLinearGroup (Fin n) A,
          τ.comp f = ρ) := by
  classical
  let : TopologicalSpace (IsLocalRing.ResidueField A) := ⊥
  let f := fundamentalGroupHom D.1.supportComplement.ι point
  let ρbar : π₁ᵉᵗ(point) →* Matrix.GeneralLinearGroup (Fin n)
      (IsLocalRing.ResidueField A) :=
    (Matrix.GeneralLinearGroup.map (IsLocalRing.residue A)).comp ρ.toMonoidHom
  change ((∃ τ : π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) A, τ.comp f = ρ) ↔
      (∃ τbar : π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) (IsLocalRing.ResidueField A),
        τbar.toMonoidHom.comp f.toMonoidHom = ρbar)) ∧
    ((∃ τ : π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) A, τ.comp f = ρ) →
      ∃! τ : π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) A, τ.comp f = ρ)
  have hsurj : Function.Surjective f := by
    rcases boundary_quotient_1_1 D hD.1 with ⟨hU, hf⟩
    let : ConnectedSpace D.1.supportComplement := hU
    exact (hf Ω point).1
  have hresidue : Continuous (IsLocalRing.residue A) := by
    have hm : IsOpen ((IsLocalRing.maximalIdeal A : Ideal A) : Set A) := by
      simpa only [pow_one] using (isAdic_iff.mp hAdic).1 1
    have : DiscreteTopology (IsLocalRing.ResidueField A) := discreteTopology_bot _
    rw [continuous_discrete_rng]
    intro y
    rcases IsLocalRing.residue_surjective (R := A) y with ⟨x, hx⟩
    have hpreimage : IsLocalRing.residue A ⁻¹' ({y} : Set (IsLocalRing.ResidueField A)) =
        (fun z : A => z - x) ⁻¹' (IsLocalRing.maximalIdeal A : Set A) := by
      ext z
      change IsLocalRing.residue A z = y ↔ z - x ∈ IsLocalRing.maximalIdeal A
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hx, sub_eq_zero]
    rw [hpreimage]
    exact hm.preimage (continuous_id.sub continuous_const)
  let reduction : Matrix.GeneralLinearGroup (Fin n) A →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (IsLocalRing.ResidueField A) :=
    { toMonoidHom := Matrix.GeneralLinearGroup.map (IsLocalRing.residue A)
      continuous_toFun := by
        apply Continuous.units_map
        exact continuous_id.matrix_map hresidue }
  constructor
  · constructor
    · rintro ⟨τ, hτ⟩
      refine ⟨reduction.comp τ, ?_⟩
      ext g : 1
      change reduction (τ (f g)) = reduction (ρ g)
      exact congrArg reduction (DFunLike.congr_fun hτ g)
    · rintro ⟨τbar, hτbar⟩
      have hpaper := perfect_kernel_2_5 D hhor hD
      let : ConnectedSpace D.1.supportComplement := hpaper.1
      have hperfect : (commutator f.ker).topologicalClosure = ⊤ :=
        (hpaper.2 Ω point).1
      let ρK : f.ker →ₜ* Matrix.GeneralLinearGroup (Fin n) A :=
        { toMonoidHom := ρ.toMonoidHom.comp f.ker.subtype
          continuous_toFun := ρ.continuous_toFun.comp continuous_subtype_val }
      have hmod : ∀ g : f.ker,
          Matrix.GeneralLinearGroup.map
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) (ρK g) = 1 := by
        intro g
        change ρbar g.1 = 1
        rw [← hτbar]
        change τbar (f g.1) = 1
        have hfg : f g.1 = 1 := MonoidHom.mem_ker.mp g.2
        exact (congrArg τbar hfg).trans (map_one τbar)
      have htrivial : ∀ g : f.ker, ρK g = 1 :=
        adic_representation_eq_one_of_dense_commutator
          (IsLocalRing.maximalIdeal A) hAdic hperfect ρK hmod
      have hker : f.ker ≤ ρ.ker := by
        intro g hg
        exact MonoidHom.mem_ker.mpr (htrivial ⟨g, hg⟩)
      let τ₀ : π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) →*
          Matrix.GeneralLinearGroup (Fin n) A :=
        f.toMonoidHom.liftOfSurjective hsurj ⟨ρ.toMonoidHom, hker⟩
      have hcomp : τ₀.comp f.toMonoidHom = ρ.toMonoidHom := by
        ext g : 1
        exact MonoidHom.liftOfRightInverse_comp_apply
          (f := f.toMonoidHom) (f_inv := Function.surjInv hsurj)
          (Function.rightInverse_surjInv hsurj) ⟨ρ.toMonoidHom, hker⟩ g
      have hcontinuous : Continuous τ₀ := by
        apply (Topology.IsQuotientMap.of_surjective_continuous
          hsurj f.continuous_toFun).continuous_iff.2
        change Continuous (τ₀.comp f.toMonoidHom)
        rw [hcomp]
        exact ρ.continuous_toFun
      refine ⟨⟨τ₀, hcontinuous⟩, ?_⟩
      apply ContinuousMonoidHom.toMonoidHom_injective
      exact hcomp
  · rintro ⟨τ, hτ⟩
    refine ⟨τ, hτ, ?_⟩
    intro τ' hτ'
    ext g : 1
    rcases hsurj g with ⟨u, rfl⟩
    exact (DFunLike.congr_fun hτ' u).trans (DFunLike.congr_fun hτ u).symm

end Yamaguchi26SolvableCoverings
