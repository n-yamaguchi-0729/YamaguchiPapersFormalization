/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import EtaleFundamentalGroups.Inertia.FiniteIdealTameFactorization
import EtaleFundamentalGroups.Inertia.NativeAbsoluteResidueFields
import EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties
import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationTameExactness
import SchemeTheory.Normalization.IntegralClosureAutomorphisms
import SchemeTheory.Normalization.NativeNormalizationPrime
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Ramification arithmetic on the original finite normalization

The tame and wild orders of a finite Galois normalization satisfy the
ramification identity with its literal inseparable residue degree. The
original DVR and field extension supply all normalization arithmetic before
the residue-field calculation is applied.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

/-- The actual tame and wild orders at a maximal prime of the original
finite Galois normalization multiply to the original ramification index
times the inseparable degree of its literal residue-field extension. All
normalization finiteness and Galois facts are supplied by the original
field extension before the residue-field arithmetic is opened. -/
theorem originalFiniteNormalizationTameOrder_mul_wildOrder_eq_ramificationIdx_mul_finInsepDegree
    (A : Type u) (K : Type v) (F : Type w)
    [rA : CommRing A] [dA : IsDomain A] [vA : IsDiscreteValuationRing A]
    [fK : Field K] [fF : Field F]
    [aAK : Algebra A K] [fAK : IsFractionRing A K]
    [aKF : Algebra K F] [aAF : Algebra A F] [tAKF : IsScalarTower A K F]
    [fKF : FiniteDimensional K F] [gKF : IsGalois K F] :
    let : IsDedekindDomain (normalizationCommAlgCat A F).carrier :=
      nativeFieldNormalization_isDedekindDomain A K F
    let : Algebra.IsIntegral A (normalizationCommAlgCat A F).carrier :=
      inferInstanceAs (Algebra.IsIntegral A (integralClosure A F))
    ∀ (Q : Ideal (normalizationCommAlgCat A F).carrier) [Q.IsMaximal],
      let : Field
          (maximalQuotientFieldObject
            (CommRingCat.of (normalizationCommAlgCat A F).carrier) Q).α :=
        (maximalQuotientFieldObject
          (CommRingCat.of (normalizationCommAlgCat A F).carrier) Q).str
      let : Algebra (IsLocalRing.ResidueField A)
          (maximalQuotientFieldObject
            (CommRingCat.of (normalizationCommAlgCat A F).carrier) Q).α :=
        integralResidueFieldAlgebra A (normalizationCommAlgCat A F) Q
      commAlgIdealTameOrder A (normalizationCommAlgCat A F) Q
          (originalFiniteNormalizationPrime_ne_bot A K F Q) *
        commAlgIdealWildOrder A (normalizationCommAlgCat A F) Q
          (originalFiniteNormalizationPrime_ne_bot A K F Q) =
        Q.ramificationIdx A * Field.finInsepDegree (IsLocalRing.ResidueField A)
          (maximalQuotientFieldObject
            (CommRingCat.of (normalizationCommAlgCat A F).carrier) Q).α := by
  intro dB iB
  let B : CommAlgCat.{w} A := normalizationCommAlgCat A F
  change IsDedekindDomain B.carrier at dB
  change Algebra.IsIntegral A B.carrier at iB
  clear_value dB iB
  have gAB : IsGaloisGroup (B.carrier ≃ₐ[A] B.carrier) A B.carrier :=
    nativeFieldNormalization_isGaloisGroup A K F
  have tAB : Module.IsTorsionFree A B.carrier :=
    nativeFieldNormalization_isTorsionFree A K F
  have fAB : Module.Finite A B.carrier :=
    nativeNormalization_finite A K (CommAlgCat.of A F) (Field.toIsField F)
  have fG : Finite (B.carrier ≃ₐ[A] B.carrier) :=
    nativeNormalization_aut_finite A K (CommAlgCat.of A F) (Field.toIsField F)
  have hnonzero : ∀ (Q : Ideal B.carrier) [Q.IsMaximal], Q ≠ ⊥ := by
    intro Q qMax
    exact originalFiniteNormalizationPrime_ne_bot A K F Q
  have hlying : ∀ (Q : Ideal B.carrier) [Q.IsMaximal],
      Q.LiesOver (IsLocalRing.maximalIdeal A) := by
    intro Q qMax
    exact normalizationCommAlgCat_liesOver_maximalIdeal Q
  change ∀ (Q : Ideal B.carrier) [Q.IsMaximal],
    let : Field (maximalQuotientFieldObject (CommRingCat.of B.carrier) Q).α :=
      (maximalQuotientFieldObject (CommRingCat.of B.carrier) Q).str
    let : Algebra (IsLocalRing.ResidueField A)
        (maximalQuotientFieldObject (CommRingCat.of B.carrier) Q).α :=
      integralResidueFieldAlgebra A B Q
    commAlgIdealTameOrder A B Q (hnonzero Q) * commAlgIdealWildOrder A B Q (hnonzero Q) =
      Q.ramificationIdx A * Field.finInsepDegree (IsLocalRing.ResidueField A)
        (maximalQuotientFieldObject (CommRingCat.of B.carrier) Q).α
  clear_value B
  clear gKF fKF tAKF aAF aKF fAK aAK fF F fK K
  intro Q qMax residueField residueAlgebra
  have : Q.LiesOver (IsLocalRing.maximalIdeal A) := hlying Q
  exact finiteIdealTameOrder_mul_wildOrder_eq_ramificationIdx_mul_finInsepDegree
    A B.carrier Q (hnonzero Q) (B.carrier ≃ₐ[A] B.carrier)

end EtaleFundamentalGroups.Inertia
