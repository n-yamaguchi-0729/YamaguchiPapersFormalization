/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.ResidueZeroPrimeIndex
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.FiniteFieldExtensions
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.PrimeOrderTest
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Henselian
import Nyll.ValuedFieldTheory.Valuation.FiniteResidueExtension

/-!
# Ab-faithfulness over residue-zero Henselian valuations

Ab-faithfulness of the residue Galois group and finite primary root groups
in its finite field extensions imply ab-faithfulness of the absolute
Galois group of the Henselian discretely valued field.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ValuationTheory.DiscreteValuationField
open ProCGroups.Abelian ProCGroups.FiniteStepSolvableQuotients

universe u v

private theorem residueZero_openLayer_prime_index_faithful
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K]
    (D : HenselianDVF.{u, v} K) [CharZero D.residueField]
    (hres : IsAbFaithful Gal(AlgebraicClosure D.residueField/D.residueField))
    (hroots : ∀ (E : Type u) [Field E] [Algebra D.residueField E]
      [FiniteDimensional D.residueField E] (p : ℕ), p.Prime →
      Finite (CommGroup.primaryComponent Eˣ p))
    (H : OpenSubgroup Gal(Ω/K))
    (N : OpenNormalSubgroup (H : Subgroup Gal(Ω/K)))
    (hprime : (N : Subgroup (H : Subgroup Gal(Ω/K))).index.Prime) :
    Function.Injective (quotientConjugationTopologicalAbelianizationMap
      (N : Subgroup (H : Subgroup Gal(Ω/K)))) := by
  let F : IntermediateField K Ω := IntermediateField.fixedField (H : Subgroup Gal(Ω/K))
  let closedH : ClosedSubgroup Gal(Ω/K) := ⟨H.toSubgroup, H.isClosed⟩
  have hfix : F.fixingSubgroup = (H : Subgroup Gal(Ω/K)) :=
    InfiniteGalois.fixingSubgroup_fixedField closedH
  have : FiniteDimensional K F := (InfiniteGalois.isOpen_iff_finite F).mp
    (by rw [hfix]; exact H.isOpen)
  have : IsAlgClosure F Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) F⟩
  let target : HenselianDVF F := FiniteExtensionLocalization.henselianDVF D
  have : D.valuation.HasExtension target.valuation :=
    FiniteExtensionLocalization.henselianDVF_hasExtension D
  have : CharZero target.residueField :=
    charZero_of_injective_algebraMap (algebraMap D.residueField target.residueField).injective
  have : FiniteDimensional D.residueField target.residueField :=
    _root_.Valuation.finiteDimensional_residueField D.valuation target.valuation
  have htarget : IsAbFaithful Gal(AlgebraicClosure target.residueField/target.residueField) :=
    isAbFaithful_absoluteGaloisGroup_of_finiteExtension hres
  have htargetRoots : ∀ (E : Type u) [Field E] [Algebra target.residueField E]
      [FiniteDimensional target.residueField E] (p : ℕ), p.Prime →
      Finite (CommGroup.primaryComponent Eˣ p) := by
    intro E hE hA hfd p hp
    let : Algebra D.residueField E :=
      ((algebraMap target.residueField E).comp
        (algebraMap D.residueField target.residueField)).toAlgebra
    have : IsScalarTower D.residueField target.residueField E :=
      IsScalarTower.of_algebraMap_eq' rfl
    have : FiniteDimensional D.residueField E :=
      FiniteDimensional.trans D.residueField target.residueField E
    exact hroots E p hp
  let e₀ : (H : Subgroup Gal(Ω/K)) ≃ₜ* F.fixingSubgroup :=
    { toMulEquiv := MulEquiv.subgroupCongr hfix.symm
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val
        (fun x => hfix.symm ▸ x.property)
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val
        (fun x => hfix ▸ x.property) }
  let e : (H : Subgroup Gal(Ω/K)) ≃ₜ* Gal(Ω/F) :=
    e₀.trans (fixingSubgroupContinuousEquiv F)
  let M : OpenNormalSubgroup Gal(Ω/F) := ProCGroups.ProC.OpenNormalSubgroup.map
    (ContinuousMonoidHom.toContinuousMonoidHom e) e.toHomeomorph.isOpenMap e.surjective N
  have hindex : (M : Subgroup Gal(Ω/F)).index =
      (N : Subgroup (H : Subgroup Gal(Ω/K))).index :=
    (N : Subgroup (H : Subgroup Gal(Ω/K))).index_map_equiv e.toMulEquiv
  have hMprime : (M : Subgroup Gal(Ω/F)).index.Prime := hindex.symm ▸ hprime
  exact quotientConjAbelianization_injective_of_continuousMulEquiv_image e N
    (residueZero_openNormal_prime_index_faithful target htarget htargetRoots M hMprime)

/-- Finite primary root groups in every finite residue extension imply
ab-faithfulness over a residue-zero Henselian discrete valuation. -/
theorem residueZero_abFaithful_of_finitePrimePowerRoots
    {K : Type u} [Field K] (D : HenselianDVF.{u, v} K) [CharZero D.residueField]
    (hres : IsAbFaithful Gal(AlgebraicClosure D.residueField/D.residueField))
    (hroots : ∀ (E : Type u) [Field E] [Algebra D.residueField E]
      [FiniteDimensional D.residueField E] (p : ℕ), p.Prime →
      Finite (CommGroup.primaryComponent Eˣ p)) :
    IsAbFaithful Gal(AlgebraicClosure K/K) := by
  have : CharZero K := by
    refine ⟨fun m n h => ?_⟩
    apply Nat.cast_injective (R := D.residueField)
    have hv : (m : D.valuation.valuationSubring) = n := Subtype.ext h
    have hr := congrArg (IsLocalRing.residue D.valuation.valuationSubring) hv
    simpa only [map_natCast] using hr
  apply isAbFaithful_iff_prime_order_test.mpr
  intro H N hprime
  have hindex : (N : Subgroup (H : Subgroup Gal(AlgebraicClosure K/K))).index.Prime := by
    rwa [(N : Subgroup (H : Subgroup Gal(AlgebraicClosure K/K))).index_eq_card]
  exact (injective_iff_ne_one_of_prime_card _ hprime).mp
    (residueZero_openLayer_prime_index_faithful D hres hroots H N hindex)

end Yamaguchi26AbfaithfulGalois
