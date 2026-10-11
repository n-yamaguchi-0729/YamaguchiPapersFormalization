/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianTorsionRoots
import Yamaguchi26AbfaithfulGalois.GroupTheory.Faithful
import Yamaguchi26AbfaithfulGalois.Kummer.ResidueZeroFaithfulness
import Yamaguchi26AbfaithfulGalois.Kummer.ResidueZeroFiniteRoots
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.GroupTheory.Torsion

/-!
# Ab-faithfulness in residue characteristic zero

Lemma `lem:residue-zero-lift` from Section 4 of `AbfatifhulGalois.tex`.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.FiniteStepSolvableQuotients
open ValuationTheory.DiscreteValuationField

universe u v

/-- Lemma 4.1: ab-faithfulness, slimness, and finiteness of every primary
root group in every finite residue extension are equivalent. -/
theorem residueZero_abFaithful_slim_iff_finitePrimePowerRoots
    {K : Type u} [Field K] (D : HenselianDVF.{u, v} K)
    [CharZero D.residueField]
    (hres : IsAbFaithful Gal(AlgebraicClosure D.residueField/D.residueField)) :
    (IsAbFaithful Gal(AlgebraicClosure K/K) ↔ IsSlim Gal(AlgebraicClosure K/K)) ∧
      (IsSlim Gal(AlgebraicClosure K/K) ↔
        ∀ (E : Type u) [Field E] [Algebra D.residueField E]
          [FiniteDimensional D.residueField E] (ℓ : ℕ),
          ℓ.Prime → Finite (CommGroup.primaryComponent Eˣ ℓ)) := by
  have hforward := finitePrimePowerRoots_of_residueZero_slim D
  have hbackward := residueZero_abFaithful_of_finitePrimePowerRoots D hres
  exact ⟨⟨isSlim_of_isAbFaithful, fun h => hbackward (hforward h)⟩,
    ⟨hforward, fun h => isSlim_of_isAbFaithful (hbackward h)⟩⟩

end Yamaguchi26AbfaithfulGalois
