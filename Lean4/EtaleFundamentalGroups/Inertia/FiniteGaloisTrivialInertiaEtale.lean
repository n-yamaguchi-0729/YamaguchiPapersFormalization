/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteGaloisInvariantNeighborhood
import EtaleFundamentalGroups.Inertia.EtaleNormalizationInertia
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Unramified.Locus

/-!
# A finite Galois normalization with trivial inertia is etale

At each original prime, the actual finite-Galois invariant-neighborhood
theorem supplies a principal localization of the inertia-fixed algebra
which is etale over the original normal domain. Trivial inertia makes the
literal inclusion of that fixed algebra bijective. Localizing its actual
algebra equivalence gives an etale principal neighborhood in the original
normalization. These neighborhoods cover its spectrum, so target-locality
of etaleness proves the original normalization algebra is etale.

No Noetherian hypothesis, residue separability hypothesis, or finiteness
of the normalization as a module is assumed.

Reference: https://stacks.math.columbia.edu/tag/0BTF
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

/-- For a finite Galois extension of the fraction field of a normal domain,
trivial original inertia at every prime makes the actual normalization
etale over that domain. This is the affine reverse implication from
condition (9) in Tag 0BTF. -/
theorem integralClosure_etale_of_all_inertia_eq_bot
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
      IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    (∀ (Q : Ideal (integralClosure A L)) [Q.IsPrime], Q.inertia Gal(L/K) = ⊥) →
      Algebra.Etale A (integralClosure A L) := by
  intro actualAction hI
  have actualComm : SMulCommClass Gal(L/K) A (integralClosure A L) := by
    constructor
    intro σ a b
    change (galRestrict A K L (integralClosure A L) σ) (a • b) =
      a • (galRestrict A K L (integralClosure A L) σ) b
    exact (galRestrict A K L (integralClosure A L) σ).toLinearMap.map_smul a b
  let B : Type w := integralClosure A L
  change Algebra.Etale A B
  have hlocal (Q : Ideal B) [Q.IsPrime] :
      ∃ b : B, b ∉ Q ∧ Algebra.Etale A (Localization.Away b) := by
    obtain ⟨f, hf, hfEtale⟩ :=
      finiteGalois_integralClosure_inertia_exists_etale_away A K L Q
    let S : Subalgebra A B := FixedPoints.subalgebra A B (Q.inertia Gal(L/K))
    have hval : Function.Bijective S.val := by
      refine ⟨Subtype.val_injective, ?_⟩
      intro b
      refine ⟨⟨b, ?_⟩, rfl⟩
      intro g
      change (g : Gal(L/K)) • b = b
      have hg : (g : Gal(L/K)) = 1 :=
        Subgroup.mem_bot.mp ((hI Q) ▸ g.property)
      rw [hg, one_smul]
    let fs : S := f
    let e : S ≃ₐ[A] B := AlgEquiv.ofBijective S.val hval
    have he : e fs = (f : B) := AlgEquiv.ofBijective_apply S.val hval fs
    let eAway : Localization.Away fs ≃ₐ[A] Localization.Away (e fs) :=
      IsLocalization.algEquivOfAlgEquiv
        (M := Submonoid.powers fs) (T := Submonoid.powers (e fs))
        (Localization.Away fs) (Localization.Away (e fs)) e
        (Submonoid.map_powers e fs)
    have : Algebra.Etale A (Localization.Away fs) := hfEtale
    have hEtale : Algebra.Etale A (Localization.Away (e fs)) :=
      Algebra.Etale.of_equiv (R := A) (A := Localization.Away fs)
        (B := Localization.Away (e fs)) eAway
    refine ⟨e fs, ?_, hEtale⟩
    rw [he]
    exact hf
  let s : Set B := {b | Algebra.Etale A (Localization.Away b)}
  have hs : Ideal.span s = ⊤ := by
    by_contra h
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal (Ideal.span s) h
    have : Q.IsMaximal := hQ
    obtain ⟨b, hb, hEtale⟩ := hlocal Q
    exact hb (hle (Ideal.subset_span hEtale))
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_span_eq_top_target s hs (by
      intro b hb
      have : Algebra.Etale A (Localization.Away b) := hb
      infer_instance)
  have : Algebra.FormallyUnramified A B := by
    apply (Algebra.formallyUnramified_iff_forall (R := A) (A := B)).mpr
    intro Q
    obtain ⟨b, hb, hEtale⟩ := hlocal Q.asIdeal
    have : Algebra.Etale A (Localization.Away b) := hEtale
    exact (Algebra.basicOpen_subset_unramifiedLocus_iff
      (R := A) (A := B) (f := b)).mpr inferInstance hb
  have : Algebra.FormallySmooth A B := by
    apply (Algebra.smoothLocus_eq_univ_iff (R := A) (A := B)).mp
    apply Set.eq_univ_iff_forall.mpr
    intro Q
    obtain ⟨b, hb, hEtale⟩ := hlocal Q.asIdeal
    have : Algebra.Etale A (Localization.Away b) := hEtale
    exact (Algebra.basicOpen_subset_smoothLocus_iff
      (R := A) (A := B) (f := b)).mpr inferInstance hb
  exact ⟨.of_formallyUnramified_and_formallySmooth, inferInstance⟩

/-- The actual normalization of a finite Galois extension is etale
exactly when all its original ideal inertia groups are trivial. -/
theorem integralClosure_etale_iff_all_inertia_eq_bot
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
      IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    Algebra.Etale A (integralClosure A L) ↔
      ∀ (Q : Ideal (integralClosure A L)) [Q.IsPrime], Q.inertia Gal(L/K) = ⊥ := by
  intro actualAction
  constructor
  · intro hEtale Q hQ
    have : Q.IsPrime := hQ
    have hEtaleNative : Algebra.Etale A (SchemeTheory.normalizationCommAlgCat A L).carrier := by
      change Algebra.Etale A (integralClosure A L)
      exact hEtale
    let Qnative : Ideal (SchemeTheory.normalizationCommAlgCat A L).carrier := Q
    have hQnative : Qnative.IsPrime := by
      change Q.IsPrime
      exact hQ
    have : Subsingleton (Q.inertia Gal(L/K)) :=
      actualNormalizationInertia_subsingleton_of_etale A K L Qnative
    exact Subgroup.eq_bot_of_subsingleton (Q.inertia Gal(L/K))
  · intro hI
    exact integralClosure_etale_of_all_inertia_eq_bot A K L hI

end EtaleFundamentalGroups.Inertia
