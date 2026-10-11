/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameMorphism
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.FiniteOriginalCanonicalTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties
import Nyll.SchemeTheory.Normalization.IntegralClosureAutomorphisms
import Nyll.SchemeTheory.Normalization.NativeNormalizationPrime
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Canonical tame exactness on the original normalization

Constructs the intrinsic canonical tame morphism and principal-unit wild subgroup from a finite
Galois extension. Proves surjectivity onto the full roots group and identifies the wild subgroup
as its kernel.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory CategoryTheory

universe u v w

/-- The chosen maximal prime of the original finite normalization is nonzero:
its contraction is the nonzero maximal ideal of the original DVR. -/
theorem originalFiniteNormalizationPrime_ne_bot
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    (Q : Ideal (normalizationCommAlgCat A F).carrier) [Q.IsMaximal] : Q ≠ ⊥ := by
  have fAB : FaithfulSMul A (normalizationCommAlgCat A F) := by
    apply (faithfulSMul_iff_algebraMap_injective A (normalizationCommAlgCat A F)).mpr
    intro a b hab
    apply IsFractionRing.injective A K
    apply (algebraMap K F).injective
    have hcoeff : algebraMap A F a = algebraMap A F b :=
      congrArg (fun x : normalizationCommAlgCat A F => x.val) hab
    exact (IsScalarTower.algebraMap_apply A K F a).symm.trans
      (hcoeff.trans (IsScalarTower.algebraMap_apply A K F b))
  have hover : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
    normalizationCommAlgCat_liesOver_maximalIdeal Q
  exact Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) Q

/-- The full roots-of-unity group of the actual intrinsic tame order at the
chosen original normalization prime. -/
def originalFiniteNormalizationTameRootsGroup
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] : GrpCat.{w} := by
  have dB : IsDedekindDomain (normalizationCommAlgCat A F) :=
    integralClosure.isDedekindDomain A K F
  exact commAlgIdealTameRootsGroup A (normalizationCommAlgCat A F) Q
    (originalFiniteNormalizationPrime_ne_bot A K F Q)

/-- The existing intrinsic canonical tame morphism, on the actual original
normalization and with all its arithmetic data supplied by the finite extension. -/
def originalFiniteNormalizationTameMorphism
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    commAlgIdealInertiaGroup A (normalizationCommAlgCat A F) Q ⟶
      originalFiniteNormalizationTameRootsGroup A K F Q := by
  have dB : IsDedekindDomain (normalizationCommAlgCat A F) :=
    integralClosure.isDedekindDomain A K F
  have fG : Finite
      (normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F) :=
    nativeNormalization_aut_finite A K (CommAlgCat.of A F) (Field.toIsField F)
  exact commAlgCanonicalTameMorphism A (normalizationCommAlgCat A F) Q
    (originalFiniteNormalizationPrime_ne_bot A K F Q)

/-- The independent principal-unit wild subgroup in intrinsic original
normalization inertia. It is defined by the existing local wild subgroup. -/
def originalFiniteNormalizationWildSubgroup
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    Subgroup (commAlgIdealInertiaGroup A (normalizationCommAlgCat A F) Q) := by
  have dB : IsDedekindDomain (normalizationCommAlgCat A F) :=
    integralClosure.isDedekindDomain A K F
  exact finiteIdealWildSubgroup (normalizationCommAlgCat A F)
    (normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F) Q
    (originalFiniteNormalizationPrime_ne_bot A K F Q)

/-- From the original finite Galois extension alone, the same intrinsic
canonical character is onto its full root group and has exactly the independently
defined principal-unit wild kernel. The original field tower is closed before
the finite inertia exactness theorem is applied. -/
theorem originalFiniteNormalizationTameMorphism_exact
    (A : Type u) (K : Type v) (F : Type w)
    [rA : CommRing A] [dA : IsDomain A] [vA : IsDiscreteValuationRing A]
    [fK : Field K] [fF : Field F]
    [aAK : Algebra A K] [fAK : IsFractionRing A K]
    [aKF : Algebra K F] [aAF : Algebra A F] [tAKF : IsScalarTower A K F]
    [fKF : FiniteDimensional K F] [gKF : IsGalois K F] :
    ∀ (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal],
      Function.Surjective (originalFiniteNormalizationTameMorphism A K F Q).hom'.toFun ∧
        (originalFiniteNormalizationTameMorphism A K F Q).hom'.ker =
          originalFiniteNormalizationWildSubgroup A K F Q := by
  let B : CommAlgCat.{w} A := normalizationCommAlgCat A F
  have dB : IsDedekindDomain B := integralClosure.isDedekindDomain A K F
  have tAF : Module.IsTorsionFree A F := .trans_faithfulSMul A K F
  have tAB : Module.IsTorsionFree A B :=
    inferInstanceAs (Module.IsTorsionFree A (integralClosure A F))
  have fAB : Module.Finite A B :=
    nativeNormalization_finite A K (CommAlgCat.of A F) (Field.toIsField F)
  have gAB : IsGaloisGroup (B ≃ₐ[A] B) A B :=
    integralClosure_automorphisms_isGaloisGroup A K F
  have fG : Finite (B ≃ₐ[A] B) :=
    nativeNormalization_aut_finite A K (CommAlgCat.of A F) (Field.toIsField F)
  have hnonzero : ∀ (Q : Ideal B) [Q.IsMaximal], Q ≠ ⊥ := by
    intro Q qMax
    exact originalFiniteNormalizationPrime_ne_bot A K F Q
  change ∀ (Q : Ideal B) [Q.IsMaximal],
    Function.Surjective (commAlgCanonicalTameMorphism A B Q (hnonzero Q)).hom'.toFun ∧
      (commAlgCanonicalTameMorphism A B Q (hnonzero Q)).hom'.ker =
        finiteIdealWildSubgroup B (B ≃ₐ[A] B) Q (hnonzero Q)
  clear_value B
  clear tAF gKF fKF tAKF aAF aKF fAK aAK fF F fK K
  intro Q qMax
  have hbaseMax : (Q.under A).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have hover : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal hbaseMax).symm⟩
  constructor
  · exact finiteOriginalCanonicalTameCharacter_surjective A B Q (hnonzero Q)
  · exact finiteOriginalCanonicalTameCharacter_ker A B Q (hnonzero Q)

end EtaleFundamentalGroups.Inertia

end
