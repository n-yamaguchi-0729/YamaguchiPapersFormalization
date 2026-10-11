/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkGenericTensor
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.StrictGenericSplittingNormal
import Nyll.SchemeTheory.RingTheory.StrictHenselianFiberDegree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The full-degree closed-fiber criterion over a normal local domain

The actual strict henselization preserves the fiber degree. Its integral
base change of the original normalization embeds into the actual generic
tensor. Lifting the split fiber's idempotents forces that generic tensor
to split. Existing descent of actual strict generic splitting then proves
étaleness of the original integral closure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- An étale closed fiber whose degree is at least the original generic
degree makes the actual normalization étale over a normal local domain.
No separability, Galoisness, or Noetherianity is assumed. -/
theorem integralClosure_etale_of_normal_local_fiber_degree
    {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]
    (L : Type u) [CommRing L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [Module.Finite (FractionRing R) L]
    [Algebra.Etale (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] integralClosure R L)]
    (hdegree : Module.finrank (FractionRing R) L ≤
      Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R ⊗[R] integralClosure R L)) :
    Algebra.Etale R (integralClosure R L) := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let K := FractionRing R
  let F := FractionRing A
  let B := integralClosure R L
  let k := IsLocalRing.ResidueField R
  let kA := IsLocalRing.ResidueField A
  let : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  have : IsLocalHom (algebraMap R A) := geometricStalkStructureMap_isLocalHom φ
  have : Module.Flat R A := (RingHom.flat_algebraMap_iff).mp
    (geometricStalkStructureMap_flat φ)
  let : Algebra K F := (geometricStalkFractionFieldMap φ).toAlgebra
  let BA := A ⊗[R] B
  let G := F ⊗[K] L
  let egeneric : (A ⊗[R] L) ≃ₐ[A] G := geometricStalkGenericTensorEquiv φ L
  let includeHom : BA →ₐ[A] (A ⊗[R] L) := Algebra.TensorProduct.lTensor (S := A) A B.val
  have hinclude : Function.Injective includeHom := by
    change Function.Injective (B.val.toLinearMap.lTensor A)
    exact Module.Flat.lTensor_preserves_injective_linearMap B.val.toLinearMap
      Subtype.val_injective
  let f : BA →ₐ[A] G := egeneric.toAlgHom.comp includeHom
  have hf : Function.Injective f := egeneric.injective.comp hinclude
  let efiber : (kA ⊗[A] BA) ≃ₐ[kA] (kA ⊗[k] (k ⊗[R] B)) :=
    (Algebra.TensorProduct.cancelBaseChange R A kA kA B).trans
      (Algebra.TensorProduct.cancelBaseChange R k kA kA B).symm
  have hsource : Algebra.Etale kA (kA ⊗[k] (k ⊗[R] B)) := inferInstance
  have : Algebra.Etale kA (kA ⊗[A] BA) := Algebra.Etale.of_equiv
    (R := kA) (A := kA ⊗[k] (k ⊗[R] B)) (B := kA ⊗[A] BA) efiber.symm
  have hdegreeA : Module.finrank F G ≤ Module.finrank kA (kA ⊗[A] BA) := by
    calc
      Module.finrank F G = Module.finrank K L := Module.finrank_baseChange
      _ ≤ Module.finrank k (k ⊗[R] B) := hdegree
      _ = Module.finrank kA (kA ⊗[k] (k ⊗[R] B)) := Module.finrank_baseChange.symm
      _ = Module.finrank kA (kA ⊗[A] BA) := efiber.symm.toLinearEquiv.finrank_eq
  obtain ⟨ι, hfinite, e⟩ :=
    SchemeTheory.exists_generic_split_of_strictHenselian_fiber_degree A F BA G f hf hdegreeA
  have : Finite ι := hfinite
  exact integralClosure_etale_of_normal_strictGeneric_tensor_split φ ι e

end EtaleFundamentalGroups.StrictHenselian
