/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealInertiaConjugate
import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertiaConjugate
import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertia
import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationDecomposition
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import EtaleFundamentalGroups.Inertia.CommAlgInertiaRingMaps
import SchemeTheory.Normalization.AmbientNormalizationGroupMap
import SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Basic

/-!
# Conjugation compatibility of normalization restriction

Proves that normalization restriction intertwines original finite-field inertia conjugation with
intrinsic normalization inertia conjugation.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The actual normalization restriction intertwines the native original
and intrinsic inertia conjugates. Both ambient actions remain in their owners. -/
theorem originalFiniteNormalizationInertiaConjugate_map
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F))
    (d : normalizationDecompositionGroup A K F Q)
    (σ : actualNormalizationInertiaGroup A K F Q) :
    (originalFiniteNormalizationInertiaMorphism A K F Q).hom'.toFun
        (originalFiniteNormalizationInertiaConjugate A K F Q d σ) =
      commAlgIdealInertiaConjugate A (normalizationCommAlgCat A F) Q
        ((originalFiniteNormalizationDecompositionMorphism A K F Q).hom'.toFun d)
        ((originalFiniteNormalizationInertiaMorphism A K F Q).hom'.toFun σ) := by
  apply commAlgIdealInertiaRingHom_injective A (normalizationCommAlgCat A F) Q
  let g : Gal(F/K) := (normalizationDecompositionInclusion A K F Q).toFun d
  let s : Gal(F/K) := actualNormalizationInertiaElement A K F Q σ
  let f : Gal(F/K) →*
      (normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F) :=
    (normalizationGaloisGroupMap A K F).hom'
  change (f.toFun (g * s * g⁻¹)).toRingHom =
    (f.toFun g * f.toFun s * (f.toFun g)⁻¹).toRingHom
  have hInv : f.toFun g⁻¹ = (f.toFun g)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    exact (f.map_mul' g⁻¹ g).symm.trans
      ((congrArg f.toFun (inv_mul_cancel g)).trans f.map_one')
  exact congrArg
    (fun e : normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F => e.toRingHom)
    ((f.map_mul' (g * s) g⁻¹).trans
      (congrArg₂
        (fun x y : normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F => x * y)
        (f.map_mul' g s) hInv))

end EtaleFundamentalGroups.Inertia

end
