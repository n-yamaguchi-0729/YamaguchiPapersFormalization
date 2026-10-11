/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Henselian.CompleteOrthogonalIdempotents
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.Away.Lemmas
import ValuedFieldTheory.Valuation.DiscreteValuationField.IntegralClosure

/-!
# Local factors of finite étale algebras over complete local rings

Finite étale algebras over a complete local ring need not themselves be
local.  Their closed fibre is a finite product of fields.  The corresponding
complete orthogonal idempotents lift through the Henselian closed-fibre map,
and split the algebra into finite étale local factors.  This file establishes
that source decomposition; the later quotient-lifting assembly can use its
factors one at a time.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped TensorProduct

universe u

/-- If a maximal ideal is contained in the Jacobson radical, it is the unique
maximal ideal. -/
theorem isLocalRing_of_isMaximal_of_le_jacobson
    {S : Type u} [CommRing S] (J : Ideal S) (hJ : J.IsMaximal)
    (hjac : J ≤ Ideal.jacobson (⊥ : Ideal S)) :
    IsLocalRing S := by
  refine IsLocalRing.of_unique_max_ideal ⟨J, hJ, ?_⟩
  intro M hM
  symm
  apply hJ.eq_of_le hM.ne_top
  exact hjac.trans (sInf_le ⟨bot_le, hM⟩)

/-- An idempotent factor of a finite algebra is finite over the same base. -/
theorem moduleFinite_quotient_span_one_sub
    {B D : Type u} [CommRing B] [CommRing D] [Algebra B D]
    [Module.Finite B D] (e : D) :
    Module.Finite B (D ⧸ Ideal.span {1 - e}) := by
  exact Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ B (Ideal.span {1 - e})).toLinearMap
    (Ideal.Quotient.mkₐ_surjective B (Ideal.span {1 - e}))

/-- An idempotent factor of an étale algebra is étale over the same base. -/
theorem etale_quotient_span_one_sub_of_isIdempotentElem
    {B D : Type u} [CommRing B] [CommRing D] [Algebra B D]
    [Algebra.Etale B D] (e : D) (he : IsIdempotentElem e) :
    Algebra.Etale B (D ⧸ Ideal.span {1 - e}) := by
  let : IsLocalization.Away e (D ⧸ Ideal.span {1 - e}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  let : Algebra.Etale D (D ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.of_isLocalizationAway e
  exact Algebra.Etale.comp B D (D ⧸ Ideal.span {1 - e})

/-- Suppose a field quotient of a finite algebra has kernel equal to the
closed-fibre ideal together with an idempotent-factor ideal.  Then that
idempotent factor is local. -/
theorem isLocalRing_quotient_span_one_sub_of_field_ker
    {B D A : Type u} [CommRing B] [IsLocalRing B]
    [CommRing D] [Algebra B D] [Module.Finite B D]
    [Field A] (e : D) (f : D →+* A) (hf : Function.Surjective f)
    (hker : RingHom.ker f =
      (maximalIdeal B).map (algebraMap B D) ⊔
        Ideal.span {1 - e}) :
    IsLocalRing (D ⧸ Ideal.span {1 - e}) := by
  let K : Ideal D := Ideal.span {1 - e}
  let Q := D ⧸ K
  let π : D →+* Q := Ideal.Quotient.mk K
  have hK : K ≤ RingHom.ker f := by
    rw [hker]
    exact le_sup_right
  let g : Q →+* A := Ideal.Quotient.lift K f hK
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨d, rfl⟩ := hf a
    exact ⟨π d, Ideal.Quotient.lift_mk K f hK⟩
  let J : Ideal D := (maximalIdeal B).map (algebraMap B D)
  have hmapJ : J.map π =
      (maximalIdeal B).map (algebraMap B Q) := by
    dsimp only [J, π, Q]
    rw [Ideal.map_map]
    rfl
  have hker_g : RingHom.ker g =
      (maximalIdeal B).map (algebraMap B Q) := by
    rw [show RingHom.ker g = (RingHom.ker f).map π by
      exact Ideal.ker_quotient_lift f hK]
    rw [hker]
    change (J ⊔ K).map π = _
    rw [Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, hmapJ]
  have hmax : ((maximalIdeal B).map (algebraMap B Q)).IsMaximal := by
    rw [← hker_g]
    exact RingHom.ker_isMaximal_of_surjective g hg
  let : Module.Finite B Q := moduleFinite_quotient_span_one_sub e
  have hjac : (maximalIdeal B).map (algebraMap B Q) ≤
      Ideal.jacobson (⊥ : Ideal Q) :=
    ideal_map_le_jacobson_bot_of_le_jacobson_bot_of_moduleFinite
      (R := B) (S := Q)
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal B))
  exact isLocalRing_of_isMaximal_of_le_jacobson _ hmax hjac

/-- The kernel of a coordinate map in a product decomposition is the kernel
of the original map together with the complementary idempotent factor. -/
theorem ker_evalRingHom_comp_ringEquiv_comp_eq_sup_of_idempotent_lift
    {D F I : Type u} [CommRing D] [CommRing F]
    [Finite I] [DecidableEq I]
    (A : I → Type u) [∀ i, CommRing (A i)]
    (q : D →+* F) (E : F ≃+* ∀ i, A i) (e : I → D)
    (hmap : q ∘ e = E.symm ∘ fun i ↦ Pi.single i 1) (i : I) :
    RingHom.ker ((Pi.evalRingHom A i).comp E.toRingHom |>.comp q) =
      RingHom.ker q ⊔ Ideal.span {1 - e i} := by
  let f : D →+* A i := ((Pi.evalRingHom A i).comp E.toRingHom).comp q
  apply le_antisymm
  · intro d hd
    have hcoord : E (q d) i = 0 := by
      rw [RingHom.mem_ker] at hd
      exact hd
    have hmul : d * e i ∈ RingHom.ker q := by
      rw [RingHom.mem_ker, map_mul]
      apply E.injective
      rw [map_mul, map_zero]
      have hei : E (q (e i)) = Pi.single i 1 := by
        calc
          E (q (e i)) = E (E.symm (Pi.single i 1)) :=
            congrArg E (congrFun hmap i)
          _ = Pi.single i 1 := E.apply_symm_apply _
      rw [hei]
      ext j
      by_cases hji : j = i
      · subst j
        simp [hcoord]
      · simp [hji]
    have hrest : d * (1 - e i) ∈ Ideal.span {1 - e i} :=
      (Ideal.span {1 - e i}).mul_mem_left d
        (Ideal.subset_span (Set.mem_singleton (1 - e i)))
    have hadd : d * e i + d * (1 - e i) ∈
        RingHom.ker q ⊔ Ideal.span {1 - e i} :=
      add_mem
        ((le_sup_left : RingHom.ker q ≤
          RingHom.ker q ⊔ Ideal.span {1 - e i}) hmul)
        ((le_sup_right : Ideal.span {1 - e i} ≤
          RingHom.ker q ⊔ Ideal.span {1 - e i}) hrest)
    convert hadd using 1
    ring
  · apply sup_le
    · intro d hd
      rw [RingHom.mem_ker] at hd ⊢
      simp [hd]
    · apply Ideal.span_le.2
      intro d hd
      simp only [Set.mem_singleton_iff] at hd
      subst d
      change E (q (1 - e i)) i = 0
      have hei : E (q (e i)) = Pi.single i 1 := by
        calc
          E (q (e i)) = E (E.symm (Pi.single i 1)) :=
            congrArg E (congrFun hmap i)
          _ = Pi.single i 1 := E.apply_symm_apply _
      rw [map_sub, map_one, map_sub, map_one, hei]
      simp

/-- The field factors of the closed fibre of a finite étale algebra over a
complete Noetherian local ring determine a complete orthogonal family of
idempotents upstairs. -/
theorem exists_closedFiber_fieldFactors_and_idempotents_lift
    {B D : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B]
    [CommRing D] [Algebra B D] [Module.Finite B D] [Algebra.Etale B D] :
    let k := ResidueField B
    let F := k ⊗[B] D
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (A : I → Type u)
      (_ : ∀ i, Field (A i)) (_ : ∀ i, Algebra k (A i))
      (E : F ≃ₐ[k] ∀ i, A i) (e : I → D),
      CompleteOrthogonalIdempotents e ∧
        (Algebra.TensorProduct.includeRight : D →ₐ[B] F) ∘ e =
          E.symm ∘ fun i ↦ Pi.single i 1 := by
  classical
  let k := ResidueField B
  let F := k ⊗[B] D
  let q : D →+* F :=
    (Algebra.TensorProduct.includeRight : D →ₐ[B] F)
  let : Module.Finite k F := inferInstance
  let : Algebra.Etale k F := Algebra.Etale.baseChange B D k
  obtain ⟨I, hI, A, hAfield, hAalg, E, -⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod k F).mp
      (inferInstance : Algebra.Etale k F)
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let (i : I) : Field (A i) := hAfield i
  let (i : I) : Algebra k (A i) := hAalg i
  let eFiber : I → F := fun i ↦ E.symm (Pi.single i 1)
  have heFiber : CompleteOrthogonalIdempotents eFiber := by
    change CompleteOrthogonalIdempotents
      (E.symm.toRingEquiv.toRingHom ∘ fun i ↦ Pi.single i 1)
    exact (CompleteOrthogonalIdempotents.single A).map E.symm.toRingHom
  have hqsurjective : Function.Surjective q := by
    have hresidue : Function.Surjective (algebraMap B k) := by
      change Function.Surjective
        (Ideal.Quotient.mk (maximalIdeal B))
      exact Ideal.Quotient.mk_surjective
    intro y
    obtain ⟨x, hx⟩ :=
      Algebra.TensorProduct.includeRight_surjective D hresidue y
    exact ⟨x, hx⟩
  let : HenselianRing D
      ((maximalIdeal B).map (algebraMap B D)) :=
    henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete
  let : HenselianRing D (RingHom.ker q) := by
    have hker : RingHom.ker q =
        (maximalIdeal B).map (algebraMap B D) := by
      simpa only [q] using
        (residueField_tensor_includeRight_ker_eq_maximalIdeal_map
          (R := B) (S := D))
    rw [hker]
    infer_instance
  obtain ⟨e, he, hmap⟩ :=
    exists_completeOrthogonalIdempotents_lift_of_surjective_henselianRing_ker
      q hqsurjective eFiber heFiber
  exact ⟨I, inferInstance, Classical.decEq I, A, hAfield, hAalg, E, e, he, by
    funext i
    exact congrFun hmap i⟩

/-- A finite étale algebra over a complete Noetherian local ring has a
complete orthogonal idempotent decomposition whose factors are finite,
étale, and local over the base.  The factors are the quotients by the
complementary idempotents lifted from the field factors of the closed fibre. -/
theorem exists_closedFiber_fieldFactors_with_finiteEtale_localFactors
    {B D : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B]
    [CommRing D] [Algebra B D] [Module.Finite B D] [Algebra.Etale B D] :
    let k := ResidueField B
    let F := k ⊗[B] D
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (A : I → Type u) (_ : ∀ i, Field (A i))
      (_ : ∀ i, Algebra k (A i))
      (E : F ≃ₐ[k] ∀ i, A i) (e : I → D),
      CompleteOrthogonalIdempotents e ∧
      (Algebra.TensorProduct.includeRight : D →ₐ[B] F) ∘ e =
        E.symm ∘ (fun i ↦ Pi.single i 1) ∧
      ∀ i,
        Module.Finite B (D ⧸ Ideal.span {1 - e i}) ∧
        Algebra.Etale B (D ⧸ Ideal.span {1 - e i}) ∧
        IsLocalRing (D ⧸ Ideal.span {1 - e i}) := by
  classical
  let k := ResidueField B
  let F := k ⊗[B] D
  obtain ⟨I, hIfin, hIdec, A, hAfield, hAalg, E, e, he, hmap⟩ :=
    exists_closedFiber_fieldFactors_and_idempotents_lift
      (B := B) (D := D)
  let : Fintype I := hIfin
  let : DecidableEq I := hIdec
  let (i : I) : Field (A i) := hAfield i
  let (i : I) : Algebra k (A i) := hAalg i
  let q : D →+* F :=
    (Algebra.TensorProduct.includeRight : D →ₐ[B] F)
  have hq : Function.Surjective q := by
    have hresidue : Function.Surjective (algebraMap B k) := by
      change Function.Surjective (Ideal.Quotient.mk (maximalIdeal B))
      exact Ideal.Quotient.mk_surjective
    intro y
    obtain ⟨x, hx⟩ :=
      Algebra.TensorProduct.includeRight_surjective D hresidue y
    exact ⟨x, hx⟩
  have hkerq : RingHom.ker q =
      (maximalIdeal B).map (algebraMap B D) := by
    simpa only [q] using
      (residueField_tensor_includeRight_ker_eq_maximalIdeal_map
        (R := B) (S := D))
  refine ⟨I, hIfin, hIdec, A, hAfield, hAalg, E, e, he, hmap, ?_⟩
  intro i
  refine ⟨moduleFinite_quotient_span_one_sub (e i),
    etale_quotient_span_one_sub_of_isIdempotentElem (e i) (he.idem i), ?_⟩
  let f : D →+* A i :=
    ((Pi.evalRingHom A i).comp E.toRingEquiv.toRingHom).comp q
  have hf : Function.Surjective f :=
    (Function.surjective_eval i).comp (E.surjective.comp hq)
  apply isLocalRing_quotient_span_one_sub_of_field_ker
    (B := B) (D := D) (A := A i) (e i) f hf
  rw [ker_evalRingHom_comp_ringEquiv_comp_eq_sup_of_idempotent_lift
    A q E.toRingEquiv e hmap i, hkerq]

end EtaleFundamentalGroups

end
