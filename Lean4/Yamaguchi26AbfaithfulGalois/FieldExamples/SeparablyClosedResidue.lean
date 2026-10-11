/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.RelativeDerivedCriterion
import Yamaguchi26AbfaithfulGalois.Kummer.MixedCharacteristicFaithfulness
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.CyclotomicOrientation
import GaloisCohomology.Kummer.Concrete.CyclotomicInfiniteImage
import ValuedFieldTheory.Ramification.HilbertRamification.SepClosedResidueDerivedProP
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.PrimePowerRoots
import ProCGroups.ProC.PrimeSeparation
import ProCGroups.ProC.Subgroups.Closed
import ProCGroups.Topologies.OpenSubgroup
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Slimness with separably closed residue field

The separably-closed-residue corollary retained from the earlier manuscript.
The residue field is required only to be separably closed.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.Abelian ProCGroups.ProC ProCGroups.FiniteStepSolvableQuotients
open ValuationTheory.DiscreteValuationField

universe u v

theorem mixedChar_separablyClosedResidue_finiteStepSolvable_slim
    {K : Type u} [Field K] [CharZero K]
    (base : HenselianDVF.{u, v} K) (p : ℕ) [Fact p.Prime]
    [CharP base.residueField p] [IsSepClosed base.residueField] :
    ∀ m : ℕ, 2 ≤ m →
      IsSlim (MaxSolvQuot Gal(AlgebraicClosure K/K) m) := by
  have hG := (isSigmaAbFaithful_absoluteGaloisGroup_singleton_of_henselian_mixedChar
    base p).isAbFaithful
  let θ : Orientation p Gal(AlgebraicClosure K/K) :=
    galoisCyclotomicOrientation p K (AlgebraicClosure K)
  have hθ : FormalHilbert90 θ :=
    formalHilbert90_galoisCyclotomicOrientation p K (AlgebraicClosure K)
  have hImage : Set.Infinite (Set.range θ) := by
    apply KummerTheory.infinite_range_cyclotomicCharacter_of_finite_primary p
    intro E hE
    have : FiniteDimensional K E := hE
    have hf := base.toDVF.finite_primePowerRoots_of_finiteExtension (L := E) p
    have : Finite {z : E | ∃ n : ℕ, z ^ (p ^ n) = 1} := hf.to_subtype
    let i : CommGroup.primaryComponent Eˣ p → {z : E | ∃ n : ℕ, z ^ (p ^ n) = 1} :=
      fun z => ⟨((z : Eˣ) : E), by
        obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.mp z.property
        exact ⟨n, congrArg Units.val hn⟩⟩
    apply Finite.of_injective i
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val hab
  have hFaithful (N : OpenNormalSubgroup Gal(AlgebraicClosure K/K)) :
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap
          (G := Gal(AlgebraicClosure K/K)) (N := (N : Subgroup Gal(AlgebraicClosure K/K)))) := by
    apply quotientConjAbelianization_injective_of_continuousMulEquiv_image
      (ProCGroups.OpenSubgroup.topContinuousMulEquiv Gal(AlgebraicClosure K/K)).symm N
    exact hG ⊤ _
  intro m hm
  let G := Gal(AlgebraicClosure K/K)
  let D : Subgroup G := topDerivedTop G (m - 1)
  have hDclosed : IsClosed (D : Set G) := inferInstance
  have hDderived : D ≤ topDerivedTop G 1 := topDerivedTop_antitone (by omega)
  have hDp := base.topDerived_hasOpenNormalBasisInClass_of_separablyClosedResidue
    p (m - 1) (by omega)
  have : CompactSpace D := hDclosed.isClosedEmbedding_subtypeVal.compactSpace
  have : TotallyDisconnectedSpace (TopologicalAbelianization D) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator D) (Subgroup.isClosed_closedCommutator D)
  have hAbp : HasOpenNormalBasisInClass (ProCGroups.FiniteGroupClass.pGroup p)
      (TopologicalAbelianization D) :=
    hDp.of_surjective
      (ProCGroups.FiniteGroupClass.pGroup_fullFormation p).melnikovFormation.formation
      (TopologicalAbelianization.mkₜ D) (TopologicalAbelianization.surjective_mk D)
  have hprime (ℓ : ℕ) [Fact ℓ.Prime]
      (hNontrivial : Nontrivial (PrimaryAbelianization ℓ D)) : ℓ = p := by
    by_contra hne
    have : Subsingleton (PrimaryAbelianization ℓ D) :=
      residualQuotient_subsingleton_of_distinct_primes p ℓ (Ne.symm hne) hAbp
    obtain ⟨a, b, hab⟩ := hNontrivial.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  have hOrient (ℓ : ℕ) [Fact ℓ.Prime]
      (hNontrivial : Nontrivial (PrimaryAbelianization ℓ D)) :
      ∃ ψ : Orientation ℓ G, RelativeFormalHilbert90 D ψ ∧ Set.Infinite (Set.range ψ) := by
    obtain rfl := hprime ℓ hNontrivial
    exact ⟨θ, (fun N _ n hn => hθ N.toOpenSubgroup n hn), hImage⟩
  have hResult := relative_centerfree_and_slim_criterion (ProfiniteGrp.of G) D hDclosed
    hDderived (fun N _ => hFaithful N)
    (fun ℓ _ hℓ => ⟨(hOrient ℓ hℓ).choose, (hOrient ℓ hℓ).choose_spec.1⟩)
  have hSlim : IsSlim (MaxSolvQuot G (m - 1 + 1)) := hResult.2 hOrient
  have hIndex : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  exact (congrArg (fun n : ℕ => IsSlim (MaxSolvQuot G n)) hIndex).mp hSlim

end Yamaguchi26AbfaithfulGalois
