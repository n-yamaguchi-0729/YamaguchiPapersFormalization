/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.GenericTensor.Refinement.NormalizationLocal

/-!
# Normalization localization at the original final tensor component

Factoring a selected component of `F' ⊗[K] L` through an intermediate field
produces a contracted component and then a second-stage component.  The
refinement of those two selected components is literally the original final
ideal.  This file consumes that equality, so subsequent normalization and
localization arguments can use the original final ideal directly.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uB uK uF uF' uL

variable {B : Type uB}
variable {K : Type uK} {F : Type uF} {F' : Type uF'} {L : Type uL}
variable [CommRing B]
variable [Field K] [Field F] [Field F'] [Field L]
variable [Algebra K F] [Algebra F F'] [Algebra K F']
variable [IsScalarTower K F F'] [Algebra K L]
variable [Algebra B F']

/-- The normalization of the original final component is canonically the
normalization of its selected second-stage component.  The source is indexed
by the literal input ideal `m`, not by a separately assumed comparison ideal. -/
noncomputable def
    genericTensorTowerFinalComponentIntegralClosureAlgEquiv
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let q := genericTensorTowerSecondIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : q.IsMaximal :=
      genericTensorTowerSecondIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let Pm := GenericTensorFieldComponent m
    let Pq := GenericTensorFieldComponent q
    letI : Algebra B Pm :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI : Algebra B Pq :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) q
    integralClosure B Pm ≃ₐ[B] integralClosure B Pq := by
  dsimp only
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let q := genericTensorTowerSecondIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : q.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  have hrefine :
      genericTensorRefineChosenComponentIdeal
          (K₀ := K) (K₁ := F) (F := F') (L := L) n q = m :=
    genericTensorRefineChosenComponentIdeal_tower_second
      (K₀ := K) (K₁ := F) (F := F') (L := L) m
  let r := genericTensorRefineChosenComponentIdeal
    (K₀ := K) (K₁ := F) (F := F') (L := L) n q
  letI : r.IsMaximal :=
    genericTensorRefineChosenComponentIdeal_isMaximal
      (K₀ := K) (K₁ := F) (F := F') (L := L) n q
  letI : Algebra B (GenericTensorFieldComponent m) :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) m
  letI : Algebra B (GenericTensorFieldComponent r) :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) r
  letI : Algebra B (GenericTensorFieldComponent q) :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) q
  let eIdealF : GenericTensorFieldComponent m ≃ₐ[F']
      GenericTensorFieldComponent r :=
    Ideal.quotientEquivAlgOfEq F' hrefine.symm
  let eIdealB : GenericTensorFieldComponent m ≃ₐ[B]
      GenericTensorFieldComponent r :=
    { toRingEquiv := eIdealF.toRingEquiv
      commutes' := by
        intro b
        change eIdealF
            (algebraMap F' (GenericTensorFieldComponent m)
              (algebraMap B F' b)) =
          algebraMap F' (GenericTensorFieldComponent r)
            (algebraMap B F' b)
        exact eIdealF.commutes (algebraMap B F' b) }
  exact eIdealB.mapIntegralClosure.trans
    (genericTensorRefineChosenComponentIntegralClosureAlgEquiv
      (B := B) (K₀ := K) (K₁ := F) (F := F') (L := L) n q)

/-- The normalization prime on the selected second-stage component obtained
by literal transport from a prime on the original final component. -/
noncomputable def
    genericTensorTowerFinalComponentIntegralClosurePrime
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let Pm := GenericTensorFieldComponent m
      letI : Algebra B Pm :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B Pm)) :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let q := genericTensorTowerSecondIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : q.IsMaximal :=
      genericTensorTowerSecondIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let Pq := GenericTensorFieldComponent q
    letI : Algebra B Pq :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) q
    Ideal (integralClosure B Pq) := by
  dsimp only at p ⊢
  exact p.map
    (genericTensorTowerFinalComponentIntegralClosureAlgEquiv
      (B := B) (K := K) (F := F) (F' := F') (L := L) m).toRingEquiv

/-- Literal transport of a normalization prime from the original final
component preserves primality. -/
theorem genericTensorTowerFinalComponentIntegralClosurePrime_isPrime
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let Pm := GenericTensorFieldComponent m
      letI : Algebra B Pm :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B Pm))
    [p.IsPrime] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let q := genericTensorTowerSecondIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : q.IsMaximal :=
      genericTensorTowerSecondIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let Pq := GenericTensorFieldComponent q
    letI : Algebra B Pq :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) q
    (genericTensorTowerFinalComponentIntegralClosurePrime
      (B := B) (K := K) (F := F) (F' := F') (L := L) m p).IsPrime := by
  dsimp only at p ⊢
  let E := genericTensorTowerFinalComponentIntegralClosureAlgEquiv
    (B := B) (K := K) (F := F) (F' := F') (L := L) m
  apply Ideal.map_isPrime_of_surjective E.surjective
  intro x hx
  have hx0 : x = 0 := E.injective (hx.trans E.map_zero.symm)
  subst x
  exact p.zero_mem

/-- Localization at a normalization prime of the literal final component is
canonically equivalent to localization at the transported prime on the
selected second-stage component. -/
noncomputable def
    genericTensorTowerFinalComponentIntegralClosureLocalizationAlgEquiv
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let Pm := GenericTensorFieldComponent m
      letI : Algebra B Pm :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B Pm))
    [p.IsPrime] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let q := genericTensorTowerSecondIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : q.IsMaximal :=
      genericTensorTowerSecondIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let Pm := GenericTensorFieldComponent m
    let Pq := GenericTensorFieldComponent q
    letI : Algebra B Pm :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI : Algebra B Pq :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) q
    let p' := genericTensorTowerFinalComponentIntegralClosurePrime
      (B := B) (K := K) (F := F) (F' := F') (L := L) m p
    letI : p'.IsPrime :=
      genericTensorTowerFinalComponentIntegralClosurePrime_isPrime
        (B := B) (K := K) (F := F) (F' := F') (L := L) m p
    Localization.AtPrime p ≃ₐ[B] Localization.AtPrime p' := by
  dsimp only
  let E := genericTensorTowerFinalComponentIntegralClosureAlgEquiv
    (B := B) (K := K) (F := F) (F' := F') (L := L) m
  let p' := genericTensorTowerFinalComponentIntegralClosurePrime
    (B := B) (K := K) (F := F) (F' := F') (L := L) m p
  letI : p'.IsPrime :=
    genericTensorTowerFinalComponentIntegralClosurePrime_isPrime
      (B := B) (K := K) (F := F) (F' := F') (L := L) m p
  have hcomap : p = p'.comap E.toRingHom := by
    symm
    exact Ideal.comap_map_of_bijective E.toRingEquiv E.bijective
  exact Localization.localAlgEquiv p p' E hcomap

end EtaleFundamentalGroups.Kummer

end
