/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitFundamentalGroupSystem
import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitEventualHom
import Nyll.SchemeTheory.FiniteEtale.InverseLimitModel
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Fundamental groups of the original qcqs inverse limit

Actual finite étale object and morphism descent supply the two inputs to
automorphism assembly.  The resulting bijection is the already-constructed
comparison whose coordinates are the original fundamental-group maps.
Compactness upgrades that same comparison to a topological group isomorphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale.InverseLimitDiagram

universe u

variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable (D : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone D) (hs : IsLimit s)
variable [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (D.map h)]
variable [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
variable [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
variable {Ω : Type u} [Field Ω] (point : Spec (.of Ω) ⟶ s.pt)

include hs in
/-- The canonical comparison for the original geometric data is bijective.
Both categorical descent inputs are supplied by actual scheme theorems. -/
theorem fundamentalGroupComparison_bijective :
    Function.Bijective (fundamentalGroupComparison D s point) := by
  have hobjects : ∀ A : FiniteEtale s.pt,
      ∃ (i : I) (B : stage D i), Nonempty ((toLimit D s i).obj B ≅ A) := by
    intro A
    obtain ⟨i, B, hB⟩ := exists_inverse_limit_model D s hs A
    exact ⟨i.unop, B, hB⟩
  have hraw : Function.Bijective (pullbackAutComparison D s point) :=
    autInverseLimitComparison_bijective (stage D) (toLimit D s) (transition D)
      (comparison D s) (fiber point) (unitIso D) (compositionIso D)
      (comparison_identity D s) (comparison_composition D s)
      hobjects (eventualHom D s hs)
  have htransport : Function.Bijective
      (fundamentalGroupSystemIso D s point).toContinuousMonoidHom :=
    (fundamentalGroupSystemIso D s point).inverseLimitContinuousMulEquiv.bijective
  exact htransport.comp hraw

/-- The original fundamental group is canonically the inverse limit of the
original stage fundamental groups, with their canonical topologies. -/
def fundamentalGroupInverseLimitEquiv :
    π₁ᵉᵗ(point) ≃ₜ* (fundamentalGroupSystem D s point).inverseLimit :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (fundamentalGroupComparison D s point).toMonoidHom
    (fundamentalGroupComparison D s point).continuous_toFun
    (fundamentalGroupComparison_bijective D s hs point)

/-- The equivalence uses the previously constructed canonical forward map. -/
theorem fundamentalGroupInverseLimitEquiv_apply (a : π₁ᵉᵗ(point)) :
    fundamentalGroupInverseLimitEquiv D s hs point a =
      fundamentalGroupComparison D s point a :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2_apply
    (fundamentalGroupComparison D s point).toMonoidHom
    (fundamentalGroupComparison D s point).continuous_toFun
    (fundamentalGroupComparison_bijective D s hs point) a

/-- The canonical equivalence retains the original cone projection maps on
fundamental groups, without a choice of an alternative system or comparison. -/
theorem fundamentalGroupInverseLimitEquiv_projection (i : I) (a : π₁ᵉᵗ(point)) :
    (fundamentalGroupSystem D s point).projection i
        (fundamentalGroupInverseLimitEquiv D s hs point a) =
      fundamentalGroupHom (s.π.app (Opposite.op i)) point a := by
  rw [fundamentalGroupInverseLimitEquiv_apply]
  exact fundamentalGroupComparison_projection D s point i a

end AlgebraicGeometry.FiniteEtale.InverseLimitDiagram
