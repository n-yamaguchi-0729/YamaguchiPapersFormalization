/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.NormalizationEtale

/-!
# Right-coordinate bijectivity through component refinement

The component-refinement equivalence preserves the literal right tensor
coordinate.  Consequently bijectivity of the right coordinate can be
composed through an intermediate selected component without assuming a
separate comparison of maps.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uK₀ uK₁ uF uL

variable {K₀ : Type uK₀} {K₁ : Type uK₁}
variable {F : Type uF} {L : Type uL}
variable [Field K₀] [Field K₁] [Field F] [Field L]
variable [Algebra K₀ K₁] [Algebra K₁ F] [Algebra K₀ F]
variable [IsScalarTower K₀ K₁ F]
variable [Algebra K₀ L]

/-- If the canonical right coordinate is bijective in the intermediate
component and again in the selected second-stage component, it is bijective
in the literally refined final component. -/
theorem genericTensorRefineChosenComponentRight_bijective
    (m : Ideal (K₁ ⊗[K₀] L)) [m.IsMaximal]
    (q : Ideal (F ⊗[K₁] GenericTensorFieldComponent m))
    [q.IsMaximal]
    (hm : Function.Bijective
      (genericTensorFieldComponentRight m))
    (hq : Function.Bijective
      (genericTensorFieldComponentRight q)) :
    let n := genericTensorRefineChosenComponentIdeal
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
    letI : n.IsMaximal :=
      genericTensorRefineChosenComponentIdeal_isMaximal
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
    Function.Bijective (genericTensorFieldComponentRight n) := by
  dsimp only
  let n := genericTensorRefineChosenComponentIdeal
    (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
  let : n.IsMaximal :=
    genericTensorRefineChosenComponentIdeal_isMaximal
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
  let E : GenericTensorFieldComponent n ≃ₐ[F]
      GenericTensorFieldComponent q :=
    genericTensorRefineChosenComponentAlgEquiv
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m q
  have hg : Function.Surjective
      ((Ideal.Quotient.mkₐ F q).comp
        (genericTensorRefineChosenComponentMap
          (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m)) :=
    Ideal.Quotient.mk_surjective.comp
      (genericTensorRefineChosenComponentMap_surjective
        (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m)
  have hmk (z : F ⊗[K₀] L) :
      E (Ideal.Quotient.mk n z) =
        (Ideal.Quotient.mkₐ F q)
          (genericTensorRefineChosenComponentMap
            (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m z) := by
    exact Ideal.quotientKerAlgEquivOfSurjective_mk hg z
  have hcoord (y : L) :
      E (genericTensorFieldComponentRight n y) =
        genericTensorFieldComponentRight q
          (genericTensorFieldComponentRight m y) := by
    change
      E (Ideal.Quotient.mk n ((1 : F) ⊗ₜ[K₀] y)) =
        Ideal.Quotient.mk q
          ((1 : F) ⊗ₜ[K₁]
            (Ideal.Quotient.mk m ((1 : K₁) ⊗ₜ[K₀] y)))
    rw [hmk]
    rw [genericTensorRefineChosenComponentMap_tmul]
    rfl
  have hcomposite : Function.Bijective
      (fun y : L ↦ E (genericTensorFieldComponentRight n y)) := by
    have hcanonical : Function.Bijective
        (fun y : L ↦ genericTensorFieldComponentRight q
          (genericTensorFieldComponentRight m y)) := by
      change Function.Bijective
        (genericTensorFieldComponentRight q ∘
          genericTensorFieldComponentRight m)
      exact hq.comp hm
    simpa only [hcoord] using hcanonical
  constructor
  · intro x y hxy
    apply hcomposite.injective
    exact congrArg E hxy
  · intro z
    obtain ⟨y, hy⟩ := hcomposite.surjective (E z)
    refine ⟨y, E.injective ?_⟩
    exact hy

/-- For an arbitrary selected final tensor component, bijectivity of the
right coordinate through its canonical intermediate and second-stage
components recovers bijectivity of the right coordinate in the original
final component. -/
theorem genericTensorTowerFinalComponentRight_bijective
    [FiniteDimensional K₁ F]
    (m : Ideal (F ⊗[K₀] L)) [m.IsMaximal] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K₀) (F := K₁) (F' := F) (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K₀) (F := K₁) (F' := F) (L := L) m
    let q := genericTensorTowerSecondIdeal
      (K := K₀) (F := K₁) (F' := F) (L := L) m
    letI : q.IsMaximal :=
      genericTensorTowerSecondIdeal_isMaximal
        (K := K₀) (F := K₁) (F' := F) (L := L) m
    Function.Bijective (genericTensorFieldComponentRight n) →
      Function.Bijective (genericTensorFieldComponentRight q) →
      Function.Bijective (genericTensorFieldComponentRight m) := by
  dsimp only
  let n := genericTensorTowerIntermediateIdeal
    (K := K₀) (F := K₁) (F' := F) (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K₀) (F := K₁) (F' := F) (L := L) m
  let q := genericTensorTowerSecondIdeal
    (K := K₀) (F := K₁) (F' := F) (L := L) m
  let : q.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal
      (K := K₀) (F := K₁) (F' := F) (L := L) m
  intro hn hq
  let r := genericTensorRefineChosenComponentIdeal
    (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) n q
  let : r.IsMaximal :=
    genericTensorRefineChosenComponentIdeal_isMaximal
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) n q
  have hrefined : Function.Bijective
      (genericTensorFieldComponentRight r) :=
    genericTensorRefineChosenComponentRight_bijective
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L)
      n q hn hq
  have hr : r = m :=
    genericTensorRefineChosenComponentIdeal_tower_second
      (K₀ := K₀) (K₁ := K₁) (F := F) (L := L) m
  let E : GenericTensorFieldComponent r ≃ₐ[F]
      GenericTensorFieldComponent m :=
    Ideal.quotientEquivAlgOfEq F hr
  have hcoord (y : L) :
      E (genericTensorFieldComponentRight r y) =
        genericTensorFieldComponentRight m y := by
    change E (Ideal.Quotient.mk r ((1 : F) ⊗ₜ[K₀] y)) =
      Ideal.Quotient.mk m ((1 : F) ⊗ₜ[K₀] y)
    exact Ideal.quotientEquivAlgOfEq_mk F hr _
  have htransported : Function.Bijective
      (fun y : L ↦ E (genericTensorFieldComponentRight r y)) := by
    change Function.Bijective
      (E ∘ genericTensorFieldComponentRight r)
    exact E.bijective.comp hrefined
  simpa only [hcoord] using htransported

end EtaleFundamentalGroups.Kummer

end
