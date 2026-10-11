/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ChosenFactor
import Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.BaseChange

/-!
# Coordinates on a complete-local chosen factor

The residue-lift classification identifies a chosen finite étale factor
`D / B` with `B ⊗[A] C`, where `C / A` is the explicit finite étale lift
of the actual residue extension.  This file reads that same equivalence in the
other direction: it equips `D` with the induced `C`-algebra structure and
identifies `D / C` with the iterated radical obtained from `B / A` by base
change.

The induced algebra structure is a named definition, not a global instance.
Consumers install it locally once, avoiding duplicate tensor-product tower
searches.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u

/-- The `C`-algebra structure on a chosen tensor factor transported by its
`B`-algebra equivalence.  This is deliberately not a global instance. -/
@[reducible]
noncomputable def tensorChosenFactorRightAlgebra
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    (e : (B ⊗[A] C) ≃ₐ[B] D) : Algebra C D :=
  ((e.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra)

/-- Swapping the tensor factors turns the chosen-factor equivalence into a
`C`-algebra equivalence for the transported right-factor action. -/
noncomputable def tensorChosenFactorCommAlgEquiv
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    (e : (B ⊗[A] C) ≃ₐ[B] D) :
    letI : Algebra C D := tensorChosenFactorRightAlgebra e
    (C ⊗[A] B) ≃ₐ[C] D := by
  letI : Algebra C D := tensorChosenFactorRightAlgebra e
  refine
    { toRingEquiv :=
        (Algebra.TensorProduct.comm A C B).toRingEquiv.trans e.toRingEquiv
      commutes' := ?_ }
  intro c
  rfl

namespace Kummer

/-- A tensor-trivialized chosen factor of an iterated radical is itself the
corresponding iterated radical over the finite residue lift. -/
noncomputable def iteratedRadicalChosenFactorAlgEquiv
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    [Algebra (iteratedRadical A r n a) D]
    (e : (iteratedRadical A r n a ⊗[A] C) ≃ₐ[iteratedRadical A r n a] D) :
    letI : Algebra C D := tensorChosenFactorRightAlgebra e
    iteratedRadical C r n (fun i ↦ algebraMap A C (a i)) ≃ₐ[C] D := by
  letI : Algebra C D := tensorChosenFactorRightAlgebra e
  exact
    (iteratedRadicalBaseChangeAlgEquiv n a).symm.trans
      (tensorChosenFactorCommAlgEquiv e)

/-- A uniquely chosen finite étale factor over a complete positive iterated
root cover whose base maximal ideal is finitely generated has actual
generalized-Kummer coordinates over the explicit finite étale lift of its
residue field.

Unlike `iteratedRadicalChosenFactorAlgEquiv`, this theorem does not assume a
tensor presentation.  It produces that presentation from finite étaleness,
the chosen closed-point factor, completeness, and residue preservation, then
returns the induced `C`-linear radical coordinates. -/
theorem exists_iteratedRadicalChosenFactorAlgEquiv_of_fg
    {A : Type u} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q),
          letI : Module.Finite A B := finite_iteratedRadical n a hn
          letI : Module.FaithfullyFlat A B :=
            faithfullyFlat_iteratedRadical n a hn
          letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
          letI : IsLocalHom (algebraMap A B) :=
            Algebra.IsIntegral.isLocalHom A B
          letI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
            isAdicComplete_maximalIdeal_iteratedRadical_of_fg
              hmax n a hn ha
          letI : IsLocalRing D :=
            isLocalRing_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap B D) :=
            isLocalHom_of_unique_prime_over_maximal q hunique
          letI : Module.FaithfullyFlat B D :=
            faithfullyFlat_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap A D) := by
            rw [IsScalarTower.algebraMap_eq A B D]
            infer_instance
          let k := IsLocalRing.ResidueField A
          let kB := IsLocalRing.ResidueField B
          let l := IsLocalRing.ResidueField D
          let eResidue : k ≃ₐ[k] kB :=
            AlgEquiv.ofBijective (Algebra.ofId k kB)
              (residueFieldMap_bijective_iteratedRadical n a hn ha)
          letI : Module.Finite k kB :=
            Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
          letI : Module.Finite k l := Module.Finite.trans kB l
          letI : Algebra.IsSeparable k kB :=
            AlgEquiv.Algebra.isSeparable eResidue
          letI : Algebra.IsSeparable k l :=
            Algebra.IsSeparable.trans k kB l
          let C := FiniteEtaleResidueLift A l
          ∃ e : (B ⊗[A] C) ≃ₐ[B] D,
            letI : Algebra C D := tensorChosenFactorRightAlgebra e
            Nonempty
              (iteratedRadical C r n (fun i ↦ algebraMap A C (a i)) ≃ₐ[C] D) := by
  dsimp only
  intro D _ _ _ _ _ _ q _ _ hunique
  let B := iteratedRadical A r n a
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a hn
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  let : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
    isAdicComplete_maximalIdeal_iteratedRadical_of_fg hmax n a hn ha
  let : IsLocalRing D :=
    isLocalRing_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  let : Module.FaithfullyFlat B D :=
    faithfullyFlat_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A B D]
    infer_instance
  let k := IsLocalRing.ResidueField A
  let kB := IsLocalRing.ResidueField B
  let l := IsLocalRing.ResidueField D
  let eResidue : k ≃ₐ[k] kB :=
    AlgEquiv.ofBijective (Algebra.ofId k kB)
      (residueFieldMap_bijective_iteratedRadical n a hn ha)
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB :=
    AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  let C := FiniteEtaleResidueLift A l
  obtain ⟨e⟩ := exists_baseChange_finiteEtaleResidueLift_algEquiv
    (R := A) (B := B) (D := D)
    (residueFieldMap_bijective_iteratedRadical n a hn ha)
  refine ⟨e, ?_⟩
  let : Algebra C D := tensorChosenFactorRightAlgebra e
  exact ⟨iteratedRadicalChosenFactorAlgEquiv n a e⟩

/-- Noetherian specialization of
`exists_iteratedRadicalChosenFactorAlgEquiv_of_fg`. -/
abbrev exists_iteratedRadicalChosenFactorAlgEquiv
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :=
  @exists_iteratedRadicalChosenFactorAlgEquiv_of_fg
    A _ _ _
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing r n a hn ha

end Kummer

end EtaleFundamentalGroups

end
