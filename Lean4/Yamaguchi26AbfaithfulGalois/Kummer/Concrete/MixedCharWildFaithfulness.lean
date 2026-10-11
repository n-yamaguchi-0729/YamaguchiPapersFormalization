/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharHenselianFaithfulness
import GaloisCohomology.Kummer.Concrete.NormalRestrictionResidualAction
import GaloisCohomology.Kummer.Concrete.NormalRestrictionKernelFinite
import GaloisCohomology.Kummer.Concrete.AbsoluteResidualAbelianizationAction
import ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import ProCGroups.FiniteGroups.PGroupFormation
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Ring.Action.End
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Faithful pro-p action for every prime extension degree

For a prime-degree Galois extension M/K of a mixed-characteristic Henselian DVF,
the relative Galois group acts faithfully on the abelianization of the actual
maximal pro-p quotient of the absolute Galois group of M. The proof uses the
canonical tower K → M → AlgebraicClosure M and its actual restriction kernel.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open ProCGroups ProCGroups.ProC ProCGroups.Abelian KummerTheory
open ValuationTheory.DiscreteValuationField

universe u v

/-- In mixed characteristic (0,p), every prime-degree Galois extension has
faithful conjugation action on the abelianization of its maximal pro-p
absolute Galois quotient. The historical wild-detection API now includes
prime extension degrees different from the residue prime. -/
theorem mixedChar_wild_residualAbelianization_faithful
    {K M : Type u} [Field K] [Field M] [Algebra K M] [IsGalois K M] [CharZero K]
    (base : HenselianDVF.{u, v} K) (p : ℕ) [Fact p.Prime]
    [CharP base.residueField p] {r : ℕ} [Fact r.Prime]
    (hdegree : Module.finrank K M = r) :
    Function.Injective (fun τ : Gal(M/K) =>
      absoluteGaloisResidualAbelianizationAction
        (FiniteGroupClass.pGroup_fullFormation p).hereditary τ.toRingEquiv) := by
  have : FiniteDimensional K M :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
  let Ω := AlgebraicClosure M
  let q : Gal(Ω/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  let N : Subgroup Gal(Ω/K) := q.ker
  have hN : IsOpen (N : Set Gal(Ω/K)) :=
    normalRestrictionKernel_isOpen (K := K) (M := M) (Ω := Ω)
  have hindex : N.index = r :=
    (normalRestrictionKernel_index (K := K) (M := M) (Ω := Ω)).trans hdegree
  have hfaith := mixedChar_henselian_openSubgroup_residualAbelianization_faithful
    base p N hN hindex
  let hC : FiniteGroupClass.FullFormation (FiniteGroupClass.pGroup p) :=
    FiniteGroupClass.pGroup_fullFormation p
  let f : Gal(M/K) →* MulAut (TopologicalAbelianization
      (Gal(Ω/M) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) Gal(Ω/M))) :=
    (absoluteGaloisResidualAbelianizationAction (K := M) hC.hereditary).comp
    (MulSemiringAction.toRingAut Gal(M/K) M)
  change Function.Injective f
  apply (injective_iff_map_eq_one f).mpr
  intro τ hτ
  by_contra hτne
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective Ω τ
  have hgN : g ∉ N := by
    intro h
    change q g = 1 at h
    exact hτne (hg.symm.trans h)
  have hdetect := (residualAbelianizationQuotientConjugation_injective_iff
    hC N (N.isClosed_of_isOpen hN)).mp hfaith g hgN
  apply hdetect
  apply MulEquiv.ext
  intro a
  let t : TopologicalAbelianization (N ⧸ proCResidualCore (FiniteGroupClass.pGroup p) N) ≃ₜ*
      TopologicalAbelianization (Gal(Ω/M) ⧸
        proCResidualCore (FiniteGroupClass.pGroup p) Gal(Ω/M)) :=
    normalRestrictionResidualAbelianizationEquiv (K := K) (M := M) hC.hereditary
  apply t.injective
  have hcomm := normalRestrictionResidualAbelianizationEquiv_conjugation
    (K := K) (M := M) hC g a
  exact hcomm.trans (DFunLike.congr_fun ((congrArg f hg).trans hτ) (t a))

end ClassFieldTower.Martinet.Shafarevich
