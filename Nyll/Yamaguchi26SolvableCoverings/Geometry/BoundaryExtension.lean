/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryInertia
import Nyll.EtaleFundamentalGroups.Inertia.ExtendableNormalizationStabilizer
import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendableCoverKernel
import Nyll.EtaleFundamentalGroups.GeometricFiber.RegularBoundarySurjective

/-!
# Boundary inertia of finite etale extensions

A cover which extends over the ambient scheme has trivial geometric-point
inertia at every boundary component. This proves one inclusion in the kernel
formula of Lemma 1.1 without requiring ambient normality or integrality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]

/-- An actual finite etale extension kills every normalized-point boundary
stabilizer. Boundary regularity supplies full faithfulness of restriction. -/
theorem isBoundaryUnramified_of_extension
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ D.1.supportComplement)
    (W : FiniteEtale D.1.supportComplement) [IsConnected W]
    (hW : ∃ V : FiniteEtale X,
      Nonempty ((FiniteEtale.pullback D.1.supportComplement.ι).obj V ≅ W)) :
    IsBoundaryUnramified D W := by
  obtain ⟨V, ⟨e⟩⟩ := hW
  intro E z _hz
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro σ hσ
  exact EtaleFundamentalGroups.Inertia.aut_eq_one_of_fixes_normalizationPoint_of_extension
    D.1.supportComplement.ι point
    (boundaryComplement_fundamentalGroupHom_surjective D hreg point) W V e z σ hσ

/-- The finite-cover kernel intersection of Lemma 1.1 lies in the kernel
of the ambient fundamental-group map. -/
theorem boundaryUnramifiedKernelIntersection_le_kernel
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ D.1.supportComplement) :
    boundaryUnramifiedKernelIntersection D point ≤
      (fundamentalGroupHom D.1.supportComplement.ι point).toMonoidHom.ker := by
  rw [fundamentalGroupHom_ker_eq_iInf_extendableGalois D.1.supportComplement.ι point
    (boundaryComplement_fundamentalGroupHom_surjective D hreg point)]
  intro g hg
  simp only [Subgroup.mem_iInf]
  intro W hW w hext
  let : IsGalois W := hW
  exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp
    (Subgroup.mem_iInf.mp hg W) hW) w)
      (isBoundaryUnramified_of_extension D hreg point W hext)

end Yamaguchi26SolvableCoverings
