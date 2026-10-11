/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameQuotientCardinality
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealWildPrimary
import Nyll.EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Wild and tame cardinalities of the original finite normalization

The finite Galois field tower supplies the actual wild prime-power order.
Its independent principal-unit subgroup realizes that cardinality, and the
same tame degree is the literal normalization-inertia quotient cardinality.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The actual wild order at a prime of the original finite normalization
is a power of its residue exponential characteristic. All finite-module
and torsion-free inputs come from the original field tower. -/
theorem originalFiniteNormalizationWildOrder_exists_expChar_pow
    (A : Type u) (K : Type v) (F : Type w)
    [rA : CommRing A] [dA : IsDomain A] [vA : IsDiscreteValuationRing A]
    [fK : Field K] [fF : Field F]
    [aAK : Algebra A K] [fAK : IsFractionRing A K]
    [aKF : Algebra K F] [aAF : Algebra A F] [tAKF : IsScalarTower A K F]
    [fKF : FiniteDimensional K F] [gKF : IsGalois K F] :
    let : IsDedekindDomain (normalizationCommAlgCat A F) :=
      integralClosure.isDedekindDomain A K F
    ∀ (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal],
      ∃ r : ℕ, commAlgIdealWildOrder A (normalizationCommAlgCat A F) Q
          (originalFiniteNormalizationPrime_ne_bot A K F Q) =
        (ringExpChar Q.ResidueField) ^ r := by
  let B : CommAlgCat.{w} A := normalizationCommAlgCat A F
  have dB : IsDedekindDomain B := integralClosure.isDedekindDomain A K F
  have tAF : Module.IsTorsionFree A F := .trans_faithfulSMul A K F
  have tAB : Module.IsTorsionFree A B :=
    inferInstanceAs (Module.IsTorsionFree A (integralClosure A F))
  have fAB : Module.Finite A B :=
    nativeNormalization_finite A K (CommAlgCat.of A F) (Field.toIsField F)
  have hnonzero : ∀ (Q : Ideal B) [Q.IsMaximal], Q ≠ ⊥ := by
    intro Q qMax
    exact originalFiniteNormalizationPrime_ne_bot A K F Q
  change ∀ (Q : Ideal B) [Q.IsMaximal],
    ∃ r : ℕ, commAlgIdealWildOrder A B Q (hnonzero Q) =
      (ringExpChar Q.ResidueField) ^ r
  clear_value B
  clear tAF gKF fKF tAKF aAF aKF fAK aAK fF F fK K
  intro Q qMax
  exact finiteIdealWildOrder_exists_expChar_pow A B Q (hnonzero Q)

/-- The independently defined wild subgroup in the actual finite
normalization has exactly the proved residue-primary wild order. -/
theorem originalFiniteNormalizationWildSubgroup_card_exists_expChar_pow
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    ∃ r : ℕ, Nat.card (originalFiniteNormalizationWildSubgroup A K F Q) =
      (ringExpChar Q.ResidueField) ^ r := by
  have dB : IsDedekindDomain (normalizationCommAlgCat A F) :=
    integralClosure.isDedekindDomain A K F
  let p : ℕ := ringExpChar Q.ResidueField
  obtain ⟨r, hr⟩ := originalFiniteNormalizationWildOrder_exists_expChar_pow A K F Q
  change commAlgIdealWildOrder A (normalizationCommAlgCat A F) Q
    (originalFiniteNormalizationPrime_ne_bot A K F Q) = p ^ r at hr
  change ∃ r : ℕ, Nat.card (originalFiniteNormalizationWildSubgroup A K F Q) = p ^ r
  clear_value p
  refine ⟨r, ?_⟩
  exact (finiteIdealWildSubgroup_card (normalizationCommAlgCat A F)
    (normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F) Q
    (originalFiniteNormalizationPrime_ne_bot A K F Q)).trans hr

/-- The actual intrinsic tame degree is the cardinality of normalization
inertia modulo its same independent wild subgroup. -/
theorem originalFiniteNormalizationTameOrder_eq_card_quotient_wild
    (A : Type u) (K : Type v) (F : Type w)
    [rA : CommRing A] [dA : IsDomain A] [vA : IsDiscreteValuationRing A]
    [fK : Field K] [fF : Field F]
    [aAK : Algebra A K] [fAK : IsFractionRing A K]
    [aKF : Algebra K F] [aAF : Algebra A F] [tAKF : IsScalarTower A K F]
    [fKF : FiniteDimensional K F] [gKF : IsGalois K F] :
    let : IsDedekindDomain (normalizationCommAlgCat A F) :=
      integralClosure.isDedekindDomain A K F
    ∀ (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal],
      commAlgIdealTameOrder A (normalizationCommAlgCat A F) Q
          (originalFiniteNormalizationPrime_ne_bot A K F Q) =
        Nat.card (commAlgIdealInertiaGroup A (normalizationCommAlgCat A F) Q ⧸
          originalFiniteNormalizationWildSubgroup A K F Q) := by
  let B : CommAlgCat.{w} A := normalizationCommAlgCat A F
  have dB : IsDedekindDomain B := integralClosure.isDedekindDomain A K F
  have hnonzero : ∀ (Q : Ideal B) [Q.IsMaximal], Q ≠ ⊥ := by
    intro Q qMax
    exact originalFiniteNormalizationPrime_ne_bot A K F Q
  change ∀ (Q : Ideal B) [Q.IsMaximal],
    commAlgIdealTameOrder A B Q (hnonzero Q) =
      Nat.card (commAlgIdealInertiaGroup A B Q ⧸
        finiteIdealWildSubgroup B (B ≃ₐ[A] B) Q (hnonzero Q))
  clear_value B
  clear gKF fKF tAKF aAF aKF fAK aAK fF F fK K
  intro Q qMax
  exact finiteIdealTameOrder_eq_card_quotient_wild B (B ≃ₐ[A] B) Q (hnonzero Q)

end EtaleFundamentalGroups.Inertia

end
