/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# The fixed field of the generic absolute Galois kernel

The kernel of the generic absolute Galois map is closed and normal. Its
fixed field is Galois over the function field. For a normal integral scheme,
the fundamental group is canonically the Galois group of this fixed field,
and the generic absolute Galois map becomes restriction of automorphisms.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- The subfield of the separable closure fixed by the generic Galois kernel. -/
def genericKernelFixedField (X : Scheme.{u}) [IsIntegral X] :
    IntermediateField X.functionField (SeparableClosure X.functionField) :=
  IntermediateField.fixedField (genericAbsoluteGaloisHom X).toMonoidHom.ker

/-- The generic kernel is normal, so its fixed field is Galois. -/
instance genericKernelFixedField_isGalois (X : Scheme.{u}) [IsIntegral X] :
    IsGalois X.functionField (genericKernelFixedField X) := by
  change IsGalois X.functionField
    (IntermediateField.fixedField (genericAbsoluteGaloisHom X).toMonoidHom.ker)
  infer_instance

private def genericClosedKernel (X : Scheme.{u}) [IsIntegral X] :
    ClosedSubgroup (SeparableClosure X.functionField ≃ₐ[X.functionField]
      SeparableClosure X.functionField) where
  toSubgroup := (genericAbsoluteGaloisHom X).toMonoidHom.ker
  isClosed' := isClosed_eq (genericAbsoluteGaloisHom X).continuous continuous_const

private local instance genericClosedKernel_normal (X : Scheme.{u}) [IsIntegral X] :
    (genericClosedKernel X).toSubgroup.Normal := by
  change (genericAbsoluteGaloisHom X).toMonoidHom.ker.Normal
  infer_instance

/-- Infinite Galois correspondence recovers the actual generic kernel
from its fixed field. -/
theorem genericKernelFixedField_fixingSubgroup (X : Scheme.{u}) [IsIntegral X] :
    (genericKernelFixedField X).fixingSubgroup =
      (genericAbsoluteGaloisHom X).toMonoidHom.ker :=
  InfiniteGalois.fixingSubgroup_fixedField (genericClosedKernel X)

private def genericFundamentalGroupMulEquiv (X : Scheme.{u})
    [IsIntegral X] [IsNormalIntegral X] :
    π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)) ≃*
      (genericKernelFixedField X ≃ₐ[X.functionField] genericKernelFixedField X) :=
  (QuotientGroup.quotientKerEquivOfSurjective
    (genericAbsoluteGaloisHom X).toMonoidHom
    (genericAbsoluteGaloisHom_surjective X)).symm.trans
      (InfiniteGalois.normalAutEquivQuotient (genericClosedKernel X))

private theorem genericFundamentalGroupMulEquiv_apply (X : Scheme.{u})
    [IsIntegral X] [IsNormalIntegral X]
    (σ : SeparableClosure X.functionField ≃ₐ[X.functionField]
      SeparableClosure X.functionField) :
    genericFundamentalGroupMulEquiv X (genericAbsoluteGaloisHom X σ) =
      AlgEquiv.restrictNormalHom (genericKernelFixedField X) σ := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    (genericAbsoluteGaloisHom X).toMonoidHom
    (genericAbsoluteGaloisHom_surjective X)
  change InfiniteGalois.normalAutEquivQuotient (genericClosedKernel X)
      (e.symm (e (QuotientGroup.mk σ))) = _
  rw [e.symm_apply_apply]
  rfl

private theorem genericFundamentalGroupMulEquiv_continuous (X : Scheme.{u})
    [IsIntegral X] [IsNormalIntegral X] :
    Continuous (genericFundamentalGroupMulEquiv X) := by
  have hq : Topology.IsQuotientMap (genericAbsoluteGaloisHom X) :=
    Topology.IsQuotientMap.of_surjective_continuous
      (genericAbsoluteGaloisHom_surjective X) (genericAbsoluteGaloisHom X).continuous
  rw [hq.continuous_iff]
  have hcomp : genericFundamentalGroupMulEquiv X ∘ genericAbsoluteGaloisHom X =
      AlgEquiv.restrictNormalHom (genericKernelFixedField X) :=
    funext (genericFundamentalGroupMulEquiv_apply X)
  rw [hcomp]
  exact InfiniteGalois.restrictNormalHom_continuous (genericKernelFixedField X)

/-- The fundamental group of a normal integral scheme is the Galois group
of the field fixed by the generic absolute Galois kernel, with its Krull topology. -/
def genericFundamentalGroupEquivGalois (X : Scheme.{u})
    [IsIntegral X] [IsNormalIntegral X] :
    π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)) ≃ₜ*
      (genericKernelFixedField X ≃ₐ[X.functionField] genericKernelFixedField X) := by
  let : T2Space (genericKernelFixedField X ≃ₐ[X.functionField] genericKernelFixedField X) :=
    krullTopology_t2
  exact ContinuousMulEquiv.mk'
    ((genericFundamentalGroupMulEquiv X).toEquiv.toHomeomorphOfContinuousClosed
      (genericFundamentalGroupMulEquiv_continuous X)
      (genericFundamentalGroupMulEquiv_continuous X).isClosedMap)
    (genericFundamentalGroupMulEquiv X).map_mul

/-- Under the fixed-field identification, the generic absolute Galois map
is precisely restriction of field automorphisms. -/
theorem genericFundamentalGroupEquivGalois_apply_genericAbsoluteGaloisHom
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (σ : SeparableClosure X.functionField ≃ₐ[X.functionField]
      SeparableClosure X.functionField) :
    genericFundamentalGroupEquivGalois X (genericAbsoluteGaloisHom X σ) =
      AlgEquiv.restrictNormalHom (genericKernelFixedField X) σ :=
  genericFundamentalGroupMulEquiv_apply X σ

end AlgebraicGeometry.FiniteEtale
