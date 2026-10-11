/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteFieldCanonicalTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertia
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationWildCardinality
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Cardinality of the original finite-field wild subgroup

The genuine normalization restriction equivalence preserves the cardinality
of the already-defined wild comap and its inertia quotient. This yields the
literal original-field wild-order and tame-order statements.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

private theorem card_comap_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (P : Subgroup H) :
    Nat.card (P.comap e.toMonoidHom) = Nat.card P := by
  rw [Subgroup.comap_equiv_eq_map_symm' e P]
  exact Subgroup.card_map_of_injective e.symm.injective

private theorem card_quotient_comap_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (P : Subgroup H) :
    Nat.card (G ⧸ P.comap e.toMonoidHom) = Nat.card (H ⧸ P) :=
  Subgroup.index_comap_of_surjective P e.surjective

/-- Cardinality transports through the actual normalization restriction
equivalence to the SAME original-field wild subgroup, which was defined
independently as a comap. -/
theorem originalFiniteFieldWildSubgroup_card
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    Nat.card (originalFiniteFieldWildSubgroup A K F Q) =
      Nat.card (originalFiniteNormalizationWildSubgroup A K F Q) :=
  card_comap_mulEquiv (originalFiniteNormalizationInertiaEquiv A K F Q)
    (originalFiniteNormalizationWildSubgroup A K F Q)

/-- The literal original finite-field wild subgroup has order a power of
the exponential characteristic of its actual normalization residue field. -/
theorem originalFiniteFieldWildSubgroup_card_exists_expChar_pow
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    ∃ r : ℕ, Nat.card (originalFiniteFieldWildSubgroup A K F Q) =
      (ringExpChar Q.ResidueField) ^ r := by
  rw [originalFiniteFieldWildSubgroup_card A K F Q]
  exact originalFiniteNormalizationWildSubgroup_card_exists_expChar_pow A K F Q

/-- In residue characteristic zero, the SAME independently defined
original-field wild subgroup is trivial. -/
theorem originalFiniteFieldWildSubgroup_eq_bot_of_charZero
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal]
    [CharZero Q.ResidueField] :
    originalFiniteFieldWildSubgroup A K F Q = ⊥ := by
  obtain ⟨r, hr⟩ := originalFiniteFieldWildSubgroup_card_exists_expChar_pow A K F Q
  apply Subgroup.eq_bot_of_card_eq
  exact hr.trans (by rw [ringExpChar.eq_one, one_pow])

/-- The same actual tame degree used by the original finite canonical
character is exactly the cardinality of original inertia modulo its SAME
independently defined wild subgroup. -/
theorem originalFiniteFieldTameOrder_eq_card_quotient_wild
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    let : IsDedekindDomain (normalizationCommAlgCat A F) :=
      integralClosure.isDedekindDomain A K F
    commAlgIdealTameOrder A (normalizationCommAlgCat A F) Q
        (originalFiniteNormalizationPrime_ne_bot A K F Q) =
      Nat.card (actualNormalizationInertiaGroup A K F Q ⧸
        originalFiniteFieldWildSubgroup A K F Q) := by
  have dB : IsDedekindDomain (normalizationCommAlgCat A F) :=
    integralClosure.isDedekindDomain A K F
  exact (originalFiniteNormalizationTameOrder_eq_card_quotient_wild A K F Q).trans
    (card_quotient_comap_mulEquiv (originalFiniteNormalizationInertiaEquiv A K F Q)
      (originalFiniteNormalizationWildSubgroup A K F Q)).symm

end EtaleFundamentalGroups.Inertia

end
