/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.FiniteEtale.ClosedPrime
import EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedCompletion
import EtaleFundamentalGroups.Kummer.IteratedRadical.BaseChange

/-!
# Completion base change of an iterated radical

The iterated radical formed after completing the base is canonically the
base change of the original iterated radical.  This file fixes the induced
algebra structure in the right-factor direction and records the local,
residue, finite-etale, and chosen-closed-prime data needed by complete-local
factor consumers.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped TensorProduct

universe u

/-- The canonical base-change coordinates for an iterated radical after
maximal-adic completion. -/
noncomputable def iteratedRadicalCompletionBaseChangeAlgEquiv
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    Ahat ⊗[A] B ≃ₐ[Ahat] Bhat :=
  iteratedRadicalBaseChangeAlgEquiv n a

/-- The original iterated radical acts on the completed iterated radical
through the right tensor factor of the canonical base-change equivalence.
This named definition avoids a global competing algebra instance. -/
@[reducible]
noncomputable def iteratedRadicalCompletionAlgebra
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    Algebra B Bhat := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  let e : Ahat ⊗[A] B ≃ₐ[Ahat] Bhat :=
    iteratedRadicalCompletionBaseChangeAlgEquiv n a
  exact
    (e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] Ahat ⊗[A] B).toRingHom).toAlgebra

/-- The canonical base-change equivalence, now read as an equivalence of
algebras over the original iterated radical. -/
noncomputable def iteratedRadicalCompletionRightAlgEquiv
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    letI : Algebra B (Ahat ⊗[A] B) :=
      Algebra.TensorProduct.rightAlgebra
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    (Ahat ⊗[A] B) ≃ₐ[B] Bhat := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  let e : Ahat ⊗[A] B ≃ₐ[Ahat] Bhat :=
    iteratedRadicalCompletionBaseChangeAlgEquiv n a
  letI : Algebra B (Ahat ⊗[A] B) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  refine
    { toRingEquiv := e.toRingEquiv
      commutes' := ?_ }
  intro b
  change e ((Algebra.TensorProduct.includeRight :
    B →ₐ[A] Ahat ⊗[A] B) b) =
      e ((Algebra.TensorProduct.includeRight :
        B →ₐ[A] Ahat ⊗[A] B) b)
  rfl

/-- Completion base change is faithfully flat over the original iterated
radical.  This is ordinary faithful-flat base change, transported through
the canonical radical coordinates. -/
theorem faithfullyFlat_iteratedRadicalCompletion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    Module.FaithfullyFlat B Bhat := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  let : Module.FaithfullyFlat A Ahat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra B (Ahat ⊗[A] B) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  let eComm : (B ⊗[A] Ahat) ≃ₐ[B] (Ahat ⊗[A] B) :=
    { toRingEquiv := (Algebra.TensorProduct.comm A B Ahat).toRingEquiv
      commutes' := by
        intro b
        change Algebra.TensorProduct.comm A B Ahat
            (b ⊗ₜ[A] (1 : Ahat)) =
          ((1 : Ahat) ⊗ₜ[A] b)
        rw [Algebra.TensorProduct.comm_tmul] }
  let e : (B ⊗[A] Ahat) ≃ₐ[B] Bhat :=
    eComm.trans (iteratedRadicalCompletionRightAlgEquiv n a)
  exact Module.FaithfullyFlat.of_linearEquiv
    (R := B) (M := B ⊗[A] Ahat) e.symm.toLinearEquiv

/-- The two coefficient maps into the completed iterated radical agree. -/
theorem iteratedRadicalCompletion_algebraMap_comp_apply
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (x : A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    algebraMap B Bhat (algebraMap A B x) =
      algebraMap Ahat Bhat (algebraMap A Ahat x) := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  let e : Ahat ⊗[A] B ≃ₐ[Ahat] Bhat :=
    iteratedRadicalCompletionBaseChangeAlgEquiv n a
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  change e (1 ⊗ₜ[A] algebraMap A B x) =
    algebraMap Ahat Bhat (algebraMap A Ahat x)
  rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  exact e.commutes (algebraMap A Ahat x)

/-- The natural map from an iterated radical to the same radical after
maximal-adic completion induces an isomorphism on residue fields. -/
theorem residueFieldMap_bijective_iteratedRadicalCompletion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    let haHat : ∀ i, algebraMap A Ahat (a i) ∈
        IsLocalRing.maximalIdeal Ahat := fun i ↦ by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) (ha i)
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical n _ hn haHat
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    letI : Module.FaithfullyFlat B Bhat :=
      faithfullyFlat_iteratedRadicalCompletion n a
    Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap B Bhat)) := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  have haHat : ∀ i, algebraMap A Ahat (a i) ∈
      IsLocalRing.maximalIdeal Ahat := fun i ↦ by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap A Ahat) (ha i)
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical n _ hn haHat
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a hn
  let : Module.FaithfullyFlat Ahat Bhat :=
    faithfullyFlat_iteratedRadical n _ hn
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  let : Module.FaithfullyFlat B Bhat :=
    faithfullyFlat_iteratedRadicalCompletion n a
  have hdiagram (y : IsLocalRing.ResidueField A) :
      IsLocalRing.ResidueField.map (algebraMap B Bhat)
          (IsLocalRing.ResidueField.map (algebraMap A B) y) =
        IsLocalRing.ResidueField.map (algebraMap Ahat Bhat)
          (IsLocalRing.ResidueField.map (algebraMap A Ahat) y) := by
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    simp only [IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue Bhat)
      (iteratedRadicalCompletion_algebraMap_comp_apply n a t)
  constructor
  · exact (IsLocalRing.ResidueField.map (algebraMap B Bhat)).injective
  · intro z
    obtain ⟨x, hx⟩ :=
      (residueFieldMap_bijective_iteratedRadical n
        (fun i ↦ algebraMap A Ahat (a i)) hn haHat).2 z
    obtain ⟨y, hy⟩ :=
      (AdicCompletion.residueField_map_bijective A).2 x
    refine ⟨IsLocalRing.ResidueField.map (algebraMap A B) y, ?_⟩
    calc
      IsLocalRing.ResidueField.map (algebraMap B Bhat)
          (IsLocalRing.ResidueField.map (algebraMap A B) y) =
          IsLocalRing.ResidueField.map (algebraMap Ahat Bhat)
            (IsLocalRing.ResidueField.map (algebraMap A Ahat) y) :=
        hdiagram y
      _ = IsLocalRing.ResidueField.map (algebraMap Ahat Bhat) x := by
        rw [hy]
      _ = z := hx

/-- The original closed-point ideal extends exactly to the closed-point
ideal of the completed iterated radical. -/
theorem maximalIdeal_map_iteratedRadicalCompletion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    let haHat : ∀ i, algebraMap A Ahat (a i) ∈
        IsLocalRing.maximalIdeal Ahat := fun i ↦ by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) (ha i)
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical n _ hn haHat
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    (IsLocalRing.maximalIdeal B).map (algebraMap B Bhat) =
      IsLocalRing.maximalIdeal Bhat := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  let T := Ahat ⊗[A] B
  have haHat : ∀ i, algebraMap A Ahat (a i) ∈
      IsLocalRing.maximalIdeal Ahat := fun i ↦ by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap A Ahat) (ha i)
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical n _ hn haHat
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a hn
  let : Module.FaithfullyFlat A Ahat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  let e : T ≃ₐ[B] Bhat := iteratedRadicalCompletionRightAlgEquiv n a
  let q := IsLocalRing.maximalIdeal B
  let qT := q.map (algebraMap B T)
  have hqTmax : qT.IsMaximal :=
    tensorProduct_map_isMaximal_of_residueFieldMap_bijective
      (R := A) (R' := Ahat) (S := B) q
      AdicCompletion.maximalIdeal_eq_map.symm
      (AdicCompletion.residueField_map_bijective A)
  let : qT.IsMaximal := hqTmax
  have hmapMax : (qT.map e.toRingEquiv.toRingHom).IsMaximal :=
    hqTmax.map_bijective e.toRingEquiv.toRingHom e.bijective
  have hmap : qT.map e.toRingEquiv.toRingHom =
      q.map (algebraMap B Bhat) := by
    rw [Ideal.map_map]
    congr 1
  rw [hmap] at hmapMax
  exact IsLocalRing.eq_maximalIdeal hmapMax

/-- Complete a local iterated radical, base-change a finite etale algebra,
and transport a specified original closed prime.  The resulting ideal is
defined by exact extension, is maximal, lies over the completed closed
point, and lives in a finite etale algebra over the completed radical.

No domain or branch-prime assertion about the completed height-two ring is
needed. -/
theorem finiteEtale_closedPrime_iteratedRadicalCompletion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    let haHat : ∀ i, algebraMap A Ahat (a i) ∈
        IsLocalRing.maximalIdeal Ahat := fun i ↦ by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) (ha i)
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical n _ hn haHat
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    ∀ {E : Type u} [CommRing E] [Algebra B E]
      [Module.Finite B E] [Algebra.Etale B E],
      ∀ (q : Ideal E) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        let Ehat := Bhat ⊗[B] E
        letI : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
        letI : Algebra E Ehat := Algebra.TensorProduct.rightAlgebra
        let qhat := q.map (algebraMap E Ehat)
        qhat.IsMaximal ∧
          qhat.LiesOver (IsLocalRing.maximalIdeal Bhat) ∧
          Module.Finite Bhat Ehat ∧ Algebra.Etale Bhat Ehat := by
  dsimp only
  intro E _ _ _ _ q _ _
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  have haHat : ∀ i, algebraMap A Ahat (a i) ∈
      IsLocalRing.maximalIdeal Ahat := fun i ↦ by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap A Ahat) (ha i)
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical n _ hn haHat
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  let : Module.FaithfullyFlat B Bhat :=
    faithfullyFlat_iteratedRadicalCompletion n a
  let Ehat := Bhat ⊗[B] E
  have hqmax : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) q <| by
        rw [← q.over_def (IsLocalRing.maximalIdeal B)]
        exact IsLocalRing.maximalIdeal.isMaximal B
  let : q.IsMaximal := hqmax
  let : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
  let : Algebra E Ehat := Algebra.TensorProduct.rightAlgebra
  let qhat := q.map (algebraMap E Ehat)
  have hgeom : qhat.IsMaximal ∧
      qhat.LiesOver (IsLocalRing.maximalIdeal Bhat) :=
    tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
      (R := B) (R' := Bhat) (S := E) q
      (maximalIdeal_map_iteratedRadicalCompletion n a hn ha)
      (residueFieldMap_bijective_iteratedRadicalCompletion n a hn ha)
  exact ⟨hgeom.1, hgeom.2, inferInstance, inferInstance⟩

end EtaleFundamentalGroups.Kummer

end
