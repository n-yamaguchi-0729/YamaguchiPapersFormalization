/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.NormalizationEtale

/-!
# Chosen-prime normalization under generic tensor component refinement

The component-refinement map keeps a previously chosen intermediate tensor
component while extending the left field.  Its kernel produces an actual
component of the original tensor product, and the resulting quotient-field
equivalence is canonical.

This file lifts that produced field equivalence first to integral closures
and then to localizations at a specified prime.  The target prime is the
literal image of the source prime, so no comparison equivalence or prime
equality is an input.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uB uK₀ uK₁ uF uL

variable {B : Type uB}
variable {K₀ : Type uK₀} {K₁ : Type uK₁}
variable {F : Type uF} {L : Type uL}
variable [CommRing B]
variable [Field K₀] [Field K₁] [Field F] [Field L]
variable [Algebra K₀ K₁] [Algebra K₁ F] [Algebra K₀ F]
variable [IsScalarTower K₀ K₁ F]
variable [Algebra K₀ L]
variable [Algebra B F]

/-- Integral closures in the actual source and refined tensor components are
canonically equivalent.  The underlying field equivalence is produced by
`genericTensorRefineChosenComponentAlgEquiv`. -/
noncomputable def
    genericTensorRefineChosenComponentIntegralClosureAlgEquiv
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal]
    (q : Ideal (F ⊗[K₁] GenericTensorFieldComponent m))
    [q.IsMaximal] :
    let n := genericTensorRefineChosenComponentIdeal
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
    letI : n.IsMaximal :=
      genericTensorRefineChosenComponentIdeal_isMaximal
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
    let Pn := GenericTensorFieldComponent n
    let Pq := GenericTensorFieldComponent q
    letI : Algebra B Pn :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) n
    letI : Algebra B Pq :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) q
    integralClosure B Pn ≃ₐ[B] integralClosure B Pq := by
  dsimp only
  let n := genericTensorRefineChosenComponentIdeal
    (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
  letI : n.IsMaximal :=
    genericTensorRefineChosenComponentIdeal_isMaximal
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
  let Pn := GenericTensorFieldComponent n
  let Pq := GenericTensorFieldComponent q
  letI : Algebra B Pn :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) n
  letI : Algebra B Pq :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) q
  let eF : Pn ≃ₐ[F] Pq :=
    genericTensorRefineChosenComponentAlgEquiv
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
  let eB : Pn ≃ₐ[B] Pq :=
    { toRingEquiv := eF.toRingEquiv
      commutes' := by
        intro b
        change eF (algebraMap F Pn (algebraMap B F b)) =
          algebraMap F Pq (algebraMap B F b)
        exact eF.commutes (algebraMap B F b) }
  exact eB.mapIntegralClosure

/-- The target normalization prime obtained by literal transport along the
produced component equivalence. -/
noncomputable def
    genericTensorRefineChosenComponentIntegralClosurePrime
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal]
    (q : Ideal (F ⊗[K₁] GenericTensorFieldComponent m))
    [q.IsMaximal]
    (p :
      let n := genericTensorRefineChosenComponentIdeal
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
      letI : n.IsMaximal :=
        genericTensorRefineChosenComponentIdeal_isMaximal
          (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
      let Pn := GenericTensorFieldComponent n
      letI : Algebra B Pn :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) n
      Ideal (integralClosure B Pn)) :
    let Pq := GenericTensorFieldComponent q
    letI : Algebra B Pq :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) q
    Ideal (integralClosure B Pq) := by
  dsimp only at p ⊢
  exact p.map
    (genericTensorRefineChosenComponentIntegralClosureAlgEquiv
      (B := B) (K₀ := K₀) (K₁ := K₁) (F := F) (L := L)
      m q).toRingEquiv

/-- Transporting a prime along the produced normalization equivalence
preserves primality. -/
theorem
    genericTensorRefineChosenComponentIntegralClosurePrime_isPrime
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal]
    (q : Ideal (F ⊗[K₁] GenericTensorFieldComponent m))
    [q.IsMaximal]
    (p :
      let n := genericTensorRefineChosenComponentIdeal
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
      letI : n.IsMaximal :=
        genericTensorRefineChosenComponentIdeal_isMaximal
          (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
      let Pn := GenericTensorFieldComponent n
      letI : Algebra B Pn :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) n
      Ideal (integralClosure B Pn))
    [p.IsPrime] :
    let Pq := GenericTensorFieldComponent q
    letI : Algebra B Pq :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) q
    (genericTensorRefineChosenComponentIntegralClosurePrime
      (B := B) (K₀ := K₀) (K₁ := K₁) (F := F) (L := L)
      m q p).IsPrime := by
  dsimp only at p ⊢
  let E := genericTensorRefineChosenComponentIntegralClosureAlgEquiv
    (B := B) (K₀ := K₀) (K₁ := K₁) (F := F) (L := L)
    m q
  apply Ideal.map_isPrime_of_surjective E.surjective
  intro x hx
  have hx0 : x = 0 := E.injective (hx.trans E.map_zero.symm)
  subst x
  exact p.zero_mem

/-- Localization at the chosen source normalization prime is canonically the
localization at its literal transported target prime. -/
noncomputable def
    genericTensorRefineChosenComponentIntegralClosureLocalizationAlgEquiv
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal]
    (q : Ideal (F ⊗[K₁] GenericTensorFieldComponent m))
    [q.IsMaximal]
    (p :
      let n := genericTensorRefineChosenComponentIdeal
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
      letI : n.IsMaximal :=
        genericTensorRefineChosenComponentIdeal_isMaximal
          (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
      let Pn := GenericTensorFieldComponent n
      letI : Algebra B Pn :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) n
      Ideal (integralClosure B Pn))
    [p.IsPrime] :
    let n := genericTensorRefineChosenComponentIdeal
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
    letI : n.IsMaximal :=
      genericTensorRefineChosenComponentIdeal_isMaximal
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
    let Pn := GenericTensorFieldComponent n
    let Pq := GenericTensorFieldComponent q
    letI : Algebra B Pn :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) n
    letI : Algebra B Pq :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) q
    let p' := genericTensorRefineChosenComponentIntegralClosurePrime
      (B := B) (K₀ := K₀) (K₁ := K₁) (F := F) (L := L)
      m q p
    letI : p'.IsPrime :=
      genericTensorRefineChosenComponentIntegralClosurePrime_isPrime
        (B := B) (K₀ := K₀) (K₁ := K₁) (F := F) (L := L)
        m q p
    Localization.AtPrime p ≃ₐ[B] Localization.AtPrime p' := by
  dsimp only
  let E := genericTensorRefineChosenComponentIntegralClosureAlgEquiv
    (B := B) (K₀ := K₀) (K₁ := K₁) (F := F) (L := L)
    m q
  let p' := genericTensorRefineChosenComponentIntegralClosurePrime
    (B := B) (K₀ := K₀) (K₁ := K₁) (F := F) (L := L)
    m q p
  letI : p'.IsPrime :=
    genericTensorRefineChosenComponentIntegralClosurePrime_isPrime
      (B := B) (K₀ := K₀) (K₁ := K₁) (F := F) (L := L)
      m q p
  have hcomap : p = p'.comap E.toRingHom := by
    symm
    exact Ideal.comap_map_of_bijective E.toRingEquiv E.bijective
  exact Localization.localAlgEquiv p p' E hcomap

end EtaleFundamentalGroups.Kummer

end
