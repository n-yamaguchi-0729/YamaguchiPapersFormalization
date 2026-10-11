/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharHenselianFaithfulness
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Henselian
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaPrimeOrderTest
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaOrdinary
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaMaximalQuotient
import Nyll.ProCGroups.FiniteGroups.PrimeSigma
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualAbelianizationMonotonicity
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientTransport
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Algebra.CharP.Algebra

/-!
# Sigma-ab-faithfulness in mixed characteristic

Each open absolute Galois subgroup is the absolute group of its actual
finite fixed field. Its Henselian discrete valuation and residue prime are
constructed from the base. Prime-index detection, including primes distinct
from the residue characteristic, therefore applies on every open layer.
The unrestricted prime-order criterion gives the full singleton-p property.
-/

namespace Yamaguchi26AbfaithfulGalois

open ValuationTheory.DiscreteValuationField KummerTheory
open ClassFieldTower.Martinet.Shafarevich
open ProCGroups ProCGroups.ProC ProCGroups.FiniteStepSolvableQuotients

universe u v

-- The fixed field need only be finite: no normality of this open layer is used.
private theorem mixedChar_openLayer_prime_index_faithful
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K]
    (base : HenselianDVF.{u, v} K) (p : ℕ) [Fact p.Prime] [CharP base.residueField p]
    (H : OpenSubgroup Gal(Ω/K)) [CompactSpace (H : Subgroup Gal(Ω/K))]
    (N : OpenNormalSubgroup (H : Subgroup Gal(Ω/K)))
    (hprime : (N : Subgroup (H : Subgroup Gal(Ω/K))).index.Prime) :
    Function.Injective (residualAbelianizationQuotientConjugation
      (FiniteGroupClass.pGroup_fullFormation p)
      (N : Subgroup (H : Subgroup Gal(Ω/K))) N.isClosed) := by
  let F : IntermediateField K Ω := IntermediateField.fixedField (H : Subgroup Gal(Ω/K))
  let closedH : ClosedSubgroup Gal(Ω/K) := ⟨H.toSubgroup, H.isClosed⟩
  have hfix : F.fixingSubgroup = (H : Subgroup Gal(Ω/K)) :=
    InfiniteGalois.fixingSubgroup_fixedField closedH
  have : FiniteDimensional K F := (InfiniteGalois.isOpen_iff_finite F).mp (by
    rw [hfix]
    exact H.isOpen)
  have : IsAlgClosure F Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) F⟩
  have : T2Space Gal(Ω/F) := krullTopology_t2 (K := F) (L := Ω)
  let target : HenselianDVF F := FiniteExtensionLocalization.henselianDVF base
  have : base.toDVF.valuation.HasExtension target.toDVF.valuation :=
    FiniteExtensionLocalization.henselianDVF_hasExtension base
  have : CharP target.residueField p :=
    (Algebra.charP_iff base.residueField target.residueField p).mp inferInstance
  let e₀ : (H : Subgroup Gal(Ω/K)) ≃ₜ* F.fixingSubgroup :=
    { toMulEquiv := MulEquiv.subgroupCongr hfix.symm
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val
        (fun x => hfix.symm ▸ x.property)
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val
        (fun x => hfix ▸ x.property) }
  let e : (H : Subgroup Gal(Ω/K)) ≃ₜ* Gal(Ω/F) := e₀.trans (fixingSubgroupContinuousEquiv F)
  let M : Subgroup Gal(Ω/F) := (N : Subgroup (H : Subgroup Gal(Ω/K))).map e.toMulEquiv.toMonoidHom
  have : M.Normal :=
    (inferInstance : (N : Subgroup (H : Subgroup Gal(Ω/K))).Normal).map
      e.toMulEquiv.toMonoidHom e.surjective
  have hM : IsOpen (M : Set Gal(Ω/F)) := e.toHomeomorph.isOpenMap N N.isOpen
  let r : ℕ := (N : Subgroup (H : Subgroup Gal(Ω/K))).index
  have : Fact r.Prime := ⟨hprime⟩
  have hindex : M.index = r := (N : Subgroup (H : Subgroup Gal(Ω/K))).index_map_equiv e.toMulEquiv
  have hfaith := mixedChar_henselian_openSubgroup_residualAbelianization_faithful
    target p M hM hindex
  exact (residualAbelianizationQuotientConjugation_injective_map_iff
    (FiniteGroupClass.pGroup_fullFormation p) e
    (N : Subgroup (H : Subgroup Gal(Ω/K))) N.isClosed).mp hfaith

/-- A Henselian discrete valuation field of mixed characteristic (0,p)
is singleton-p-ab-faithful, including all finite relative quotient orders. -/
theorem isSigmaAbFaithful_absoluteGaloisGroup_singleton_of_henselian_mixedChar
    {K : Type u} [Field K] [CharZero K]
    (base : HenselianDVF.{u, v} K) (p : ℕ) [Fact p.Prime] [CharP base.residueField p] :
    IsSigmaAbFaithful {p} Gal(AlgebraicClosure K/K) := by
  apply isSigmaAbFaithful_iff_prime_order_test.mpr
  intro H
  have : CompactSpace (H : Subgroup Gal(AlgebraicClosure K/K)) :=
    H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  intro N hprime
  have hfaith := mixedChar_openLayer_prime_index_faithful base p H N hprime
  have hSigma := residualAbelianizationQuotientConjugation_injective_of_class_inclusion
    (FiniteGroupClass.pGroup_fullFormation p) (FiniteGroupClass.sigmaGroup_fullFormation {p})
    (fun {Q : Type u} [Group Q] hQ => (FiniteGroupClass.sigmaGroup_singleton_iff_pGroup p Q).mpr hQ)
    (N : Subgroup (H : Subgroup Gal(AlgebraicClosure K/K))) N.isClosed hfaith
  exact (injective_iff_ne_one_of_prime_card
    (residualAbelianizationQuotientConjugation (FiniteGroupClass.sigmaGroup_fullFormation {p})
      (N : Subgroup (H : Subgroup Gal(AlgebraicClosure K/K))) N.isClosed) hprime).mp hSigma

/-- Every Sigma containing the residue prime gives full Sigma-ab-faithfulness,
ordinary ab-faithfulness, and ordinary ab-faithfulness of the actual maximal
pro-Sigma quotient. -/
theorem isSigmaAbFaithful_absoluteGaloisGroup_and_maximalProSigma_of_henselian_mixedChar
    {K : Type u} [Field K] [CharZero K]
    (base : HenselianDVF.{u, v} K) (p : ℕ) [Fact p.Prime] [CharP base.residueField p]
    {sigma : Set ℕ} (hp : p ∈ sigma) :
    IsSigmaAbFaithful sigma Gal(AlgebraicClosure K/K) ∧
      IsAbFaithful Gal(AlgebraicClosure K/K) ∧
        IsAbFaithful (Gal(AlgebraicClosure K/K) ⧸
          proCResidualCore (FiniteGroupClass.sigmaGroup sigma) Gal(AlgebraicClosure K/K)) := by
  have hG : IsSigmaAbFaithful sigma Gal(AlgebraicClosure K/K) :=
    IsSigmaAbFaithful.mono (Set.singleton_subset_iff.mpr hp)
      (isSigmaAbFaithful_absoluteGaloisGroup_singleton_of_henselian_mixedChar base p)
  exact ⟨hG, hG.isAbFaithful, hG.isAbFaithful_residualQuotient⟩

end Yamaguchi26AbfaithfulGalois
