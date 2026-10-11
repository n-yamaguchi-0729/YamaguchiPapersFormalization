/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Ramification.NativeMaximalResidue
import SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The residue exact sequence for an actual DVR normalization

A maximal prime of the literal normalization contracts to the closed point
by the existing integral-closure prime theorem. Thus the already constructed
residue-action target is exactly the quotient automorphism group over the
native base residue field. The canonical quotient-to-prime-residue
 equivalence identifies the other field and preserves its coefficient map.
The final endpoint retains the same native decomposition map and inertia.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The actual contracted normalization prime is the closed point, by integrality. -/
theorem normalizationResidueBaseIdeal_eq_maximalIdeal
    (A : Type u) (L : Type w) [CommRing A] [IsLocalRing A]
    [Field L] [Algebra A L] (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal] :
    nativeAlgebraResidueBaseIdeal (normalizationCommAlgCat A L) Q =
      IsLocalRing.maximalIdeal A := by
  let Q₀ : Ideal (integralClosure A L) := Q
  have : Q₀.IsMaximal := by
    change Q.IsMaximal
    infer_instance
  change Q₀.under A = IsLocalRing.maximalIdeal A
  exact StrictHenselian.integralClosure_maximalPrime_under A L Q₀

/-- The actual quotient automorphism group over the native base residue field. -/
def normalizationResidueAutomorphismsOverResidueField
    (A : Type u) (L : Type w) [CommRing A] [IsLocalRing A]
    [Field L] [Algebra A L] (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal] :
    GrpCat.{w} := by
  have : Q.LiesOver (nativeAlgebraResidueBaseIdeal (normalizationCommAlgCat A L) Q) := by
    change Q.LiesOver (Q.under A)
    infer_instance
  exact nativeResidueAutomorphismsOverResidueField A (normalizationCommAlgCat A L)
    (nativeAlgebraResidueBaseIdeal (normalizationCommAlgCat A L) Q) Q
    (normalizationResidueBaseIdeal_eq_maximalIdeal A L Q)

/-- The already constructed target is exactly the actual base residue target. -/
theorem normalizationResidueAutomorphisms_eq_overResidueField
    (A : Type u) (L : Type w) [CommRing A] [IsLocalRing A]
    [Field L] [Algebra A L] (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal] :
    normalizationResidueAutomorphisms A L Q =
      normalizationResidueAutomorphismsOverResidueField A L Q := by
  have : Q.LiesOver (nativeAlgebraResidueBaseIdeal (normalizationCommAlgCat A L) Q) := by
    change Q.LiesOver (Q.under A)
    infer_instance
  exact nativeResidueAutomorphisms_eq_overResidueField A (normalizationCommAlgCat A L)
    (nativeAlgebraResidueBaseIdeal (normalizationCommAlgCat A L) Q) Q
    (normalizationResidueBaseIdeal_eq_maximalIdeal A L Q)

/-- The literal normalization quotient is canonically its prime residue field. -/
def normalizationMaximalQuotientResidueEquiv
    (A : Type u) (L : Type w) [CommRing A] [CommRing L] [Algebra A L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal] :
    ((normalizationCommAlgCat A L) ⧸ Q) ≃+* Q.ResidueField :=
  maximalQuotientResidueEquiv Q

/-- The canonical identification preserves the original normalization coefficients. -/
theorem normalizationMaximalQuotientResidueEquiv_comp_quotient
    (A : Type u) (L : Type w) [CommRing A] [CommRing L] [Algebra A L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal] :
    (normalizationMaximalQuotientResidueEquiv A L Q).toRingHom.comp (Ideal.Quotient.mk Q) =
      algebraMap (normalizationCommAlgCat A L) Q.ResidueField :=
  maximalQuotientResidueEquiv_comp_quotient Q

attribute [local instance] normalizationCommAlgGaloisAction

/-- The original DVR normalization residue sequence: the native target is
identified over the base residue field, the actual decomposition map is
surjective, and its kernel included in the Galois group is exactly inertia.
The canonical source-field identification is
`normalizationMaximalQuotientResidueEquiv`. -/
theorem normalizationResidueDVR_exact
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal] :
    nativeAlgebraResidueBaseIdeal (normalizationCommAlgCat A L) Q =
        IsLocalRing.maximalIdeal A ∧
      normalizationResidueAutomorphisms A L Q =
        normalizationResidueAutomorphismsOverResidueField A L Q ∧
      Function.Surjective (normalizationResidueMorphism A K L Q).hom'.toFun ∧
      (normalizationResidueMorphism A K L Q).hom'.ker.map
        (normalizationDecompositionInclusion A K L Q) = Q.inertia Gal(L/K) :=
  ⟨normalizationResidueBaseIdeal_eq_maximalIdeal A L Q,
    normalizationResidueAutomorphisms_eq_overResidueField A L Q,
    normalizationResidueMorphism_surjective A K L Q,
    normalizationResidueMorphism_map_ker A K L Q⟩

end EtaleFundamentalGroups.Inertia
