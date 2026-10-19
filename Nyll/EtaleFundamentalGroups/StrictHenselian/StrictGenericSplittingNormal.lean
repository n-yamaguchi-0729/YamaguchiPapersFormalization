/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAffineGenericDescent
import Nyll.EtaleFundamentalGroups.StrictHenselian.AffineNeighborhoodFaithfullyFlat
import Nyll.SchemeTheory.RingTheory.FieldExtensions.GenericTensorSplit
import Nyll.SchemeTheory.RingTheory.Etale.IntegralClosureEtaleOfSplit
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Localization.FractionRing


/-!
# Strict generic splitting and normalization over a normal local domain

A splitting over the actual strict generic field descends to an actual pointed
affine étale neighborhood. Its actual section algebra is faithfully flat.
The concrete tensor cancellation and commutation comparison then supplies the
generic-fiber splitting used by normal-localization and integral-closure descent.
No finite presentation of the original fraction field over its base is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Restore the original scalar dictionary after the canonical Under
construction. The scalar-map identity, including its induced tensor action,
is supplied by `toAlgebra_algebraMap`. -/
private def mkUnderTensorSplit
    {K : CommRingCat.{u}} {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (ι : Type u)
    (e : ((CommRingCat.mkUnder K A) ⊗[K] B) ≃ₐ[CommRingCat.mkUnder K A]
      (ι → CommRingCat.mkUnder K A)) :
    (A ⊗[K] B) ≃ₐ[A] (ι → A) := by
  change (letI : Algebra K A := (algebraMap K A).toAlgebra
    (A ⊗[K] B) ≃ₐ[A] (ι → A)) at e
  exact Eq.mp (congrArg (fun scalar : Algebra K A =>
    letI : Algebra K A := scalar
    (A ⊗[K] B) ≃ₐ[A] (ι → A)) (toAlgebra_algebraMap (R := K) (S := A))) e

/-- An actual strict-generic splitting of a finite fraction-field algebra
makes its actual integral closure étale over the original normal local domain. -/
theorem integralClosure_etale_of_normal_strictGeneric_tensor_split
    {R Ω B : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    [Field Ω] [IsSepClosed Ω] [CommRing B]
    [Algebra R B] [Algebra (FractionRing R) B]
    [IsScalarTower R (FractionRing R) B] [Module.Finite (FractionRing R) B]
    (φ : R →+* Ω) [IsLocalHom φ] (ι : Type u) [Finite ι] :
    let : Algebra (FractionRing R)
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
      (geometricStalkFractionFieldMap φ).toAlgebra
    Nonempty ((FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⊗[FractionRing R] B)
      ≃ₐ[FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))]
        (ι → FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))) →
    Algebra.Etale R (integralClosure R B) := by
  intro scalarAction he
  obtain ⟨e⟩ := he
  obtain ⟨V, v, hV, eV, -⟩ := geometricStalk_exists_affine_generic_split φ ι e
  have : IsAffine V.left := hV
  let S := Γ(V.left, ⊤)
  let : Algebra R S :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom.toAlgebra
  obtain ⟨hEtale, hFlat⟩ := affineNeighborhood_structure_etale_faithfullyFlat φ V v
  have : Algebra.Etale R S := hEtale
  have : Module.FaithfullyFlat R S := hFlat
  apply SchemeTheory.integralClosure_etale_of_generic_split_after_faithfullyFlat_etale R S B ι
  exact SchemeTheory.genericTensorSplitEquiv R (FractionRing R) S B ι
    (mkUnderTensorSplit (K := CommRingCat.of (FractionRing R))
      (A := FractionRing R ⊗[R] S) (B := B) ι eV)

end EtaleFundamentalGroups.StrictHenselian
