/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.HigherLocalField.Basic
import Yamaguchi26AbfaithfulGalois.HigherLocalField.PositiveCharacteristic
import Yamaguchi26AbfaithfulGalois.GroupTheory.Faithful
import Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaOrdinary
import Yamaguchi26AbfaithfulGalois.Kummer.MixedCharacteristicFaithfulness
import Yamaguchi26AbfaithfulGalois.Kummer.ResidueZeroFaithfulness
import Mathlib.Algebra.CharP.Defs
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Torsion

/-!
# Prime-power roots of unity and ab-faithfulness in higher local fields

The stronger joint root-finiteness and ab-faithfulness statement supporting
current Theorem 4.2 (`thm:main-hlf`) of `AbfatifhulGalois.tex`.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.FiniteStepSolvableQuotients

universe u v

/-- Every primary root group of a higher local field is finite. -/
theorem finite_primaryComponent_of_higherLocalField
    (n : ℕ) (K : Type u) [Field K]
    (hK : ValuationTheory.IsHigherLocalField.{u, v} n K) :
    ∀ (ℓ : ℕ), ℓ.Prime → Finite (CommGroup.primaryComponent Kˣ ℓ) := by
  have ht : Finite (CommGroup.torsion Kˣ) :=
    ValuationTheory.IsHigherLocalField.finite_torsion n K hK
  intro ℓ hℓ
  let f : CommGroup.primaryComponent Kˣ ℓ → CommGroup.torsion Kˣ :=
    fun z => ⟨z.1, by
      obtain ⟨m, hm⟩ := (CommGroup.mem_primaryComponent).mp z.2
      exact (CommGroup.mem_torsion z.1).mpr
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨ℓ ^ m, pow_pos hℓ.pos m, hm⟩)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : CommGroup.torsion Kˣ => (z : Kˣ)) hab
  exact Finite.of_injective f hf

/-- The characteristic-zero induction uses mixed-characteristic faithfulness
at the first positive residue characteristic and the residue-zero lifting theorem
at each preceding level. -/
theorem higher_local_field_abFaithful_of_charZero
    (n : ℕ) (K : Type u) [Field K] [CharZero K]
    (hK : ValuationTheory.IsHigherLocalField.{u, v} n K) (hn : 0 < n) :
    IsAbFaithful Gal(AlgebraicClosure K/K) := by
  induction n generalizing K with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ n ih =>
    obtain ⟨D, hD⟩ := hK
    rcases CharP.exists' D.residueField with hzero | ⟨p, hp, hres⟩
    · have : CharZero D.residueField := hzero
      have hn : 0 < n := by
        by_contra hn
        have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        have : Finite D.residueField := hD
        exact not_finite D.residueField
      have hfaithful := ih D.residueField hD hn
      apply residueZero_abFaithful_of_finitePrimePowerRoots D.toHenselianDVF hfaithful
      intro E hfield halg hfinite ℓ hℓ
      have hE := ValuationTheory.IsHigherLocalField.of_finiteExtension
        n D.residueField E hD
      exact finite_primaryComponent_of_higherLocalField n E hE ℓ hℓ
    · have : Fact p.Prime := hp
      have : CharP D.residueField p := hres
      exact (isSigmaAbFaithful_absoluteGaloisGroup_singleton_of_henselian_mixedChar
        D.toHenselianDVF p).isAbFaithful

/-- Every higher local field has finitely many roots of `ℓ`-power order
for each prime `ℓ`. In positive dimension its absolute Galois group is
ab-faithful. -/
theorem higher_local_field_roots_and_abFaithful
    (n : ℕ) (K : Type u) [Field K]
    (hK : ValuationTheory.IsHigherLocalField.{u, v} n K) :
    (∀ (ℓ : ℕ), ℓ.Prime → Finite (CommGroup.primaryComponent Kˣ ℓ)) ∧
      (0 < n → IsAbFaithful Gal(AlgebraicClosure K/K)) := by
  have hroots := finite_primaryComponent_of_higherLocalField n K hK
  refine ⟨hroots, ?_⟩
  intro hn
  rcases CharP.exists' K with hzero | ⟨p, hp, hchar⟩
  · have : CharZero K := hzero
    exact higher_local_field_abFaithful_of_charZero n K hK hn
  · have : Fact p.Prime := hp
    have : CharP K p := hchar
    exact higher_local_field_abFaithful_of_charP n K p hK hn

end Yamaguchi26AbfaithfulGalois
