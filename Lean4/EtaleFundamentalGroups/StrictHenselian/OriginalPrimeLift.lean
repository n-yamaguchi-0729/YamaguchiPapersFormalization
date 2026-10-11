/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FilteredColimit.CoconeLeg
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkAlgebraColimit
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import SchemeTheory.RingTheory.TensorProductPrime
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic


/-!
# An original prime lifts to the actual geometric-stalk tensor product

The geometric field is constructed from the original prime's residue field.
The actual stalk evaluation computes the contraction of its maximal ideal.
The existing compatible-prime tensor-product theorem then constructs a prime
with both prescribed contractions. No tensor induction or auxiliary point is
assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- The geometric point of the base induced by the original prime of its algebra. -/
def originalPrimeGeometricPoint
    (B : Type u) {R : Type u} [CommRing B] [CommRing R] [Algebra B R]
    (q : Ideal R) [q.IsPrime] : B →+* AlgebraicClosure q.ResidueField :=
  ((algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)).comp
    (algebraMap R q.ResidueField)).comp (algebraMap B R)

/-- An original prime lifts above the closed point of the actual geometric
stalk, retaining its exact contraction to the original algebra. -/
theorem geometricStalk_exists_tensorProduct_prime_over_original
    (B R : Type u) [CommRing B] [CommRing R] [Algebra B R]
    (q : Ideal R) [q.IsPrime] :
    let φ : B →+* AlgebraicClosure q.ResidueField := originalPrimeGeometricPoint B q
    let A := (geometricStalkSmallAlgebraCocone φ).pt
    let : Algebra B A := EtaleFundamentalGroups.underCommRingCatAlgebra A
    letI : IsLocalRing A := geometricStalk_isLocalRing (Spec.map (CommRingCat.ofHom φ))
    ∃ Q : PrimeSpectrum (A ⊗[B] R),
      Q.asIdeal.comap (algebraMap A (A ⊗[B] R)) = IsLocalRing.maximalIdeal A ∧
        Q.asIdeal.comap
          (Algebra.TensorProduct.includeRight (R := B) (A := A)).toRingHom = q := by
  let Ω := AlgebraicClosure q.ResidueField
  let φ : B →+* Ω := originalPrimeGeometricPoint B q
  let A := (geometricStalkSmallAlgebraCocone φ).pt
  let : Algebra B A := EtaleFundamentalGroups.underCommRingCatAlgebra A
  let : IsLocalRing A := geometricStalk_isLocalRing (Spec.map (CommRingCat.ofHom φ))
  let p : PrimeSpectrum A := ⟨IsLocalRing.maximalIdeal A, inferInstance⟩
  let q' : PrimeSpectrum R := ⟨q, inferInstance⟩
  let ev : A →+* Ω :=
    (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom
  have heval : RingHom.ker ev = IsLocalRing.maximalIdeal A := by
    change RingHom.ker
        (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom =
      IsLocalRing.maximalIdeal (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
    rw [RingHom.ker_eq_comap_bot, ← IsLocalRing.maximalIdeal_eq_bot (R := Ω)]
    exact IsLocalRing.maximalIdeal_comap
      (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom
  have hcomp : ev.comp (algebraMap B A) = φ :=
    geometricStalkStructureMap_evaluation φ
  let ψ : R →+* Ω :=
    (algebraMap q.ResidueField Ω).comp (algebraMap R q.ResidueField)
  have hψ : RingHom.ker ψ = q :=
    (RingHom.ker_comp_of_injective (algebraMap R q.ResidueField)
      (algebraMap q.ResidueField Ω).injective).trans
        (Ideal.ker_algebraMap_residueField q)
  have hφ : RingHom.ker φ = q.comap (algebraMap B R) := by
    calc
      RingHom.ker φ = RingHom.ker (ψ.comp (algebraMap B R)) := rfl
      _ = (RingHom.ker ψ).comap (algebraMap B R) :=
        (RingHom.comap_ker ψ (algebraMap B R)).symm
      _ = q.comap (algebraMap B R) :=
        congrArg (fun I : Ideal R => I.comap (algebraMap B R)) hψ
  have h : PrimeSpectrum.comap (algebraMap B A) p =
      PrimeSpectrum.comap (algebraMap B R) q' := by
    apply PrimeSpectrum.ext
    change (IsLocalRing.maximalIdeal A).comap (algebraMap B A) =
      q.comap (algebraMap B R)
    calc
      (IsLocalRing.maximalIdeal A).comap (algebraMap B A) =
          (RingHom.ker ev).comap (algebraMap B A) :=
        congrArg (fun I : Ideal A => I.comap (algebraMap B A)) heval.symm
      _ = RingHom.ker (ev.comp (algebraMap B A)) :=
        RingHom.comap_ker ev (algebraMap B A)
      _ = RingHom.ker φ := congrArg RingHom.ker hcomp
      _ = q.comap (algebraMap B R) := hφ
  obtain ⟨Q, hQp, hQq⟩ :=
    PrimeSpectrum.exists_tensorProduct_of_comap_eq B A R p q' h
  exact ⟨Q, congrArg PrimeSpectrum.asIdeal hQp, congrArg PrimeSpectrum.asIdeal hQq⟩

end EtaleFundamentalGroups.StrictHenselian
