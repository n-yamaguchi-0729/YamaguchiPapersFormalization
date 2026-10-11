/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.Faithful
import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureConjugation
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationQuotientFaithfulness
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianResidueAction
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian

/-!
# Detection through the actual residue Galois quotient

Residue ab-faithfulness detects quotient conjugation on every open normal
subgroup that contains the actual inertia kernel.
-/

namespace Yamaguchi26AbfaithfulGalois

open IsLocalRing KummerTheory ValuationTheory.DiscreteValuationField
open ProCGroups.Abelian ProCGroups.FiniteStepSolvableQuotients
open RamificationTheory.HilbertRamification.ValuationSubring

universe u v w x

/-- An open normal subgroup containing the inertia kernel has faithful quotient
conjugation whenever the actual residue Galois group is ab-faithful. -/
theorem henselian_openNormal_faithful_of_inertia_le
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (D : HenselianDVF.{u, w} K)
    {Γ : Type x} [LinearOrderedCommGroupWithZero Γ]
    (vΩ : _root_.Valuation Ω Γ) [D.valuation.HasExtension vΩ]
    (hres : IsAbFaithful Gal(ResidueField vΩ.valuationSubring/D.residueField))
    (N : OpenNormalSubgroup Gal(Ω/K))
    (hI : (henselianResidueAction D.valuation vΩ).ker ≤ (N : Subgroup Gal(Ω/K))) :
    Function.Injective (quotientConjugationTopologicalAbelianizationMap
      (N : Subgroup Gal(Ω/K))) := by
  let f := henselianResidueContinuousHom D.valuation vΩ
  have hopen : IsOpenMap f := (henselianResidueAction_isOpenQuotientMap D.valuation vΩ).isOpenMap
  have hsurj : Function.Surjective f := henselianResidueAction_surjective D.valuation vΩ
  let M := ProCGroups.ProC.OpenNormalSubgroup.map f hopen hsurj N
  have : ((N : Subgroup Gal(Ω/K)).map f.toMonoidHom).Normal := M.isNormal'
  apply quotientConjugationTopologicalAbelianizationMap_injective_of_map f
    (N : Subgroup Gal(Ω/K)) hI
  exact inj_quotientConjugationTopologicalAbelianizationMap_of_openNormalSubgroupTop
    M (hres ⊤ (openNormalSubgroupTop M))

/-- Residue ab-faithfulness on its standard algebraic closure gives the same
unramified quotient detection for any algebraic closure upstairs. -/
theorem residueZero_openNormal_faithful_of_inertia_le
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] [CharZero K]
    (D : HenselianDVF.{u, w} K) [CharZero D.residueField]
    {Γ : Type x} [LinearOrderedCommGroupWithZero Γ]
    (vΩ : _root_.Valuation Ω Γ) [D.valuation.HasExtension vΩ]
    (hres : IsAbFaithful Gal(AlgebraicClosure D.residueField/D.residueField))
    (N : OpenNormalSubgroup Gal(Ω/K))
    (hI : (henselianResidueAction D.valuation vΩ).ker ≤ (N : Subgroup Gal(Ω/K))) :
    Function.Injective (quotientConjugationTopologicalAbelianizationMap
      (N : Subgroup Gal(Ω/K))) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : IsAlgClosure D.residueField (ResidueField vΩ.valuationSubring) :=
    henselianResidueExtension_isAlgClosure D.valuation vΩ
  have hactual : IsAbFaithful Gal(ResidueField vΩ.valuationSubring / D.residueField) :=
    isAbFaithful_of_continuousMulEquiv
      (absoluteGaloisClosureEquiv D.residueField (ResidueField vΩ.valuationSubring)) hres
  exact henselian_openNormal_faithful_of_inertia_le D vΩ hactual N hI

end Yamaguchi26AbfaithfulGalois
