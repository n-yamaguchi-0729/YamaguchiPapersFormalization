/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FieldExamples.SubfieldMixedCharacteristic
import Nyll.Yamaguchi26AbfaithfulGalois.FieldExamples.SubfieldRoots
import Nyll.Yamaguchi26AbfaithfulGalois.FieldExamples.PadicFiniteTypeRoots
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem3Dot6MixedCharacteristic
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaOrdinary

/-!
# Abelian faithfulness of sub-p-adic fields

An embedding into an essentially finite-type p-adic extension supplies
abelian faithfulness and finiteness of primary roots of unity in every
finite extension of the embedded field.
-/

namespace Yamaguchi26AbfaithfulGalois
open ProCGroups.FiniteStepSolvableQuotients
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
universe u v

/-- Sub-p-adic fields have a mixed-characteristic discrete valuation and finite
primary roots in all finite extensions. The embedding is the sole sub-p-adic datum. -/
theorem subpadic_isAbFaithful_and_finite_roots
    (p : ℕ) [Fact p.Prime] (K : Type u) (E : Type v)
    [Field K] [Field E] [Algebra (Padic p) E] [Algebra.EssFiniteType (Padic p) E]
    (f : K →+* E) :
    IsAbFaithful Gal(AlgebraicClosure K/K) ∧
      ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L],
        ∀ (ℓ : ℕ) [Fact ℓ.Prime], Finite (CommGroup.primaryComponent Lˣ ℓ) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic p) E).injective
  have : CharZero K := charZero_of_inj_zero (fun n hn => by
    apply (Nat.cast_eq_zero (R := E)).mp
    rw [← map_natCast f n, hn, map_zero])
  have : CharP (padicCompleteDVF p).residueField p := padicCompleteDVF_residue_char p
  obtain ⟨D, hD⟩ := exists_mixedChar_DVF_of_essFiniteType (Padic p) E (padicCompleteDVF p).toDVF p
  have : CharP D.residueField p := hD
  obtain ⟨DK, hDK⟩ := exists_mixedChar_DVF_of_embedding f D p
  have : CharP DK.residueField p := hDK
  refine ⟨(mixed_characteristic_properties_3_6 K DK p).2.isAbFaithful, ?_⟩
  intro L _ _ _ ℓ _
  let : Algebra K E := f.toAlgebra
  apply finite_primaryComponent_finiteExtension_of_subfield K E ℓ _ L
  intro T hT
  have : FiniteDimensional E T := hT
  have : Algebra.EssFiniteType E T := Algebra.EssFiniteType.of_finiteType E T
  have : Algebra.EssFiniteType (Padic p) T := Algebra.EssFiniteType.comp (Padic p) E T
  have : Finite (CommGroup.torsion Tˣ) := finite_torsion_of_essFiniteType_padic p T
  have hle : CommGroup.primaryComponent Tˣ ℓ ≤ CommGroup.torsion Tˣ := by
    intro z hz
    obtain ⟨n, hn⟩ := hz
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨ℓ ^ n, pow_pos (Fact.out : ℓ.Prime).pos n, hn⟩
  exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end Yamaguchi26AbfaithfulGalois
