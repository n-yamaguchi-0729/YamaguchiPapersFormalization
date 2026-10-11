/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.InverseLimitFundamentalGroup

/-!
# The canonical inverse system of original geometric fundamental groups

This is the stagewise transport of the actual pullback automorphism system.
Both the transition maps and the forward comparison coordinates are proved
equal to the existing fundamental-group homomorphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open ProCGroups.InverseSystems

namespace AlgebraicGeometry.FiniteEtale.InverseLimitDiagram

universe u

variable {I : Type u} [Preorder I]
variable (D : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone D)
variable {Ω : Type u} [Field Ω] (point : Spec (.of Ω) ⟶ s.pt)

/-- The actual pullback-fiber comparison is an isomorphism of the canonical
topological automorphism groups. -/
def stageEquiv (i : I) :
    Aut (toLimit D s i ⋙ fiber point) ≃ₜ* π₁ᵉᵗ(stagePoint D s point i) :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (stageFiberIso D s point i).conjAut.toMonoidHom
    (continuous_conjAut (stageFiberIso D s point i))
    (stageFiberIso D s point i).conjAut.bijective

/-- The stage equivalence uses the canonical conjugation formula. -/
theorem stageEquiv_apply (i : I) (a : Aut (toLimit D s i ⋙ fiber point)) :
    stageEquiv D s point i a = (stageFiberIso D s point i).conjAut a :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2_apply
    (stageFiberIso D s point i).conjAut.toMonoidHom
    (continuous_conjAut (stageFiberIso D s point i))
    (stageFiberIso D s point i).conjAut.bijective a

/-- The original stage transition, expressed through the canonical fiber
comparisons so that its topology and group structure are retained. -/
def fundamentalGroupTransition {i j : I} (hij : i ≤ j) :
    π₁ᵉᵗ(stagePoint D s point j) →ₜ* π₁ᵉᵗ(stagePoint D s point i) where
  toMonoidHom := (stageEquiv D s point i).toMulEquiv.toMonoidHom.comp
    ((stageAutRestriction (stage D) (toLimit D s) (transition D) (comparison D s)
      (fiber point) hij).toMonoidHom.comp
      (stageEquiv D s point j).symm.toMulEquiv.toMonoidHom)
  continuous_toFun := (stageEquiv D s point i).continuous_toFun.comp
    ((stageAutRestriction (stage D) (toLimit D s) (transition D) (comparison D s)
      (fiber point) hij).continuous_toFun.comp
      (stageEquiv D s point j).continuous_invFun)

/-- The transported transition is exactly the original fundamental-group map
along the given scheme transition, after the cone-induced point equality. -/
theorem fundamentalGroupTransition_apply {i j : I} (hij : i ≤ j)
    (a : π₁ᵉᵗ(stagePoint D s point j)) :
    fundamentalGroupTransition D s point hij a =
      stagePoint_comp D s point hij ▸
        fundamentalGroupHom (transitionMap D hij) (stagePoint D s point j) a := by
  have h := stageAutRestriction_eq_fundamentalGroupHom D s point hij
    ((stageEquiv D s point j).symm a)
  rw [← stageEquiv_apply, ← stageEquiv_apply, ContinuousMulEquiv.apply_symm_apply] at h
  exact h

/-- The single canonical system of original stage fundamental groups. -/
@[reducible] def fundamentalGroupSystem : InverseSystem (I := I) where
  X i := π₁ᵉᵗ(stagePoint D s point i)
  topologicalSpace i := inferInstance
  map hij := fundamentalGroupTransition D s point hij
  continuous_map hij := (fundamentalGroupTransition D s point hij).continuous_toFun
  map_id i := by
    funext a
    change stageEquiv D s point i
      ((pullbackAutSystem D s point).map (le_rfl : i ≤ i)
        ((stageEquiv D s point i).symm a)) = a
    rw [(pullbackAutSystem D s point).map_id_apply,
      ContinuousMulEquiv.apply_symm_apply]
  map_comp {i j k} hij hjk := by
    funext a
    change stageEquiv D s point i
      ((pullbackAutSystem D s point).map hij
        ((stageEquiv D s point j).symm (stageEquiv D s point j
          ((pullbackAutSystem D s point).map hjk ((stageEquiv D s point k).symm a))))) =
      stageEquiv D s point i ((pullbackAutSystem D s point).map (hij.trans hjk)
        ((stageEquiv D s point k).symm a))
    rw [ContinuousMulEquiv.symm_apply_apply, (pullbackAutSystem D s point).map_comp_apply]

/-- The canonical system has the group laws carried by its continuous homomorphisms. -/
instance fundamentalGroupSystem_isGroupSystem :
    IsGroupSystem (fundamentalGroupSystem D s point) where
  map_one hij := (fundamentalGroupTransition D s point hij).map_one
  map_mul hij a b := (fundamentalGroupTransition D s point hij).map_mul a b
  map_inv hij a := (fundamentalGroupTransition D s point hij).map_inv a

/-- The stagewise identification uses the existing inverse-system-isomorphism API. -/
def fundamentalGroupSystemIso : InverseSystem.InverseSystemIso
    (pullbackAutSystem D s point) (fundamentalGroupSystem D s point) where
  stageEquiv := stageEquiv D s point
  comm {i j} hij a := by
    change stageEquiv D s point i ((pullbackAutSystem D s point).map hij a) =
      stageEquiv D s point i ((pullbackAutSystem D s point).map hij
        ((stageEquiv D s point j).symm (stageEquiv D s point j a)))
    rw [ContinuousMulEquiv.symm_apply_apply]

/-- The forward comparison into the original stage fundamental groups. -/
def fundamentalGroupComparison :
    π₁ᵉᵗ(point) →ₜ* (fundamentalGroupSystem D s point).inverseLimit :=
  (fundamentalGroupSystemIso D s point).toContinuousMonoidHom.comp
    (pullbackAutComparison D s point)

/-- Every forward coordinate is the existing fundamental-group homomorphism
of the original cone projection. -/
theorem fundamentalGroupComparison_projection (i : I) (a : π₁ᵉᵗ(point)) :
    (fundamentalGroupSystem D s point).projection i (fundamentalGroupComparison D s point a) =
      fundamentalGroupHom (s.π.app (Opposite.op i)) point a := by
  change stageEquiv D s point i
      (globalAutRestriction (stage D) (toLimit D s) (fiber point) i a) =
    fundamentalGroupHom (s.π.app (Opposite.op i)) point a
  rw [stageEquiv_apply]
  exact globalAutRestriction_eq_fundamentalGroupHom D s point i a

end AlgebraicGeometry.FiniteEtale.InverseLimitDiagram
