/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk
import Nyll.AlgebraicCurves.Geometry.Schemes.valuationRing_stalk_of_smoothOfRelativeDimension_one
import Nyll.AlgebraicCurves.Geometry.Schemes.smoothOfRelativeDimension_of_irreducibleSpace

/-!
# Scheme exists iso comp eq of is Open Immersion of is Proper
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace ProperCurveExtension

variable {K : Type u} [Field K]

private theorem existence {Y S : Scheme.{u}} (g : Y ⟶ S) [IsProper g] :
    ValuativeCriterion.Existence g := by
  have h : IsProper g := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1.existence

theorem isSeparated_of_isSeparated_over {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K))
    [IsSeparated g] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

theorem isDominant_ι {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : IsDominant U.ι :=
  ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact U.2.dense hU⟩

section Totalise

variable {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  [IsIntegral X] [IsProper sY] (hval : ∀ x : X, ValuationRing (X.presheaf.stalk x))
  (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX)

include hval hf in
theorem domain_eq_top : f.toRationalMap.domain = ⊤ :=
  top_unique fun x _ =>
    Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk sX sY (existence sY) f hf x
      (hval x)

/-- Extend a partial map to the whole source using its valuation-ring stalks. -/
def extend : X ⟶ Y :=
  have : Y.IsSeparated := isSeparated_of_isSeparated_over sY
  X.topIso.inv ≫ X.homOfLE (domain_eq_top sX sY hval f hf).ge ≫ f.toRationalMap.toPartialMap.hom

theorem ι_extend : f.domain.ι ≫ extend sX sY hval f hf = f.hom := by
  let _ : Y.IsSeparated := isSeparated_of_isSeparated_over sY
  have key : X.homOfLE f.le_domain_toRationalMap ≫ f.toRationalMap.toPartialMap.hom = f.hom :=
    f.toPartialMap_toRationalMap_restrict
  have hfactor : f.domain.ι ≫ X.topIso.inv ≫
      X.homOfLE (domain_eq_top sX sY hval f hf).ge = X.homOfLE f.le_domain_toRationalMap := by
    apply (cancel_mono f.toRationalMap.domain.ι).1
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.toIso_inv_ι, Category.comp_id]
  let t : X ⟶ (f.toRationalMap.toPartialMap.domain : Scheme.{u}) :=
    X.topIso.inv ≫ X.homOfLE (domain_eq_top sX sY hval f hf).ge
  change f.domain.ι ≫ (t ≫ f.toRationalMap.toPartialMap.hom) = f.hom
  exact (Category.assoc f.domain.ι t f.toRationalMap.toPartialMap.hom).symm.trans
    ((congrArg (fun g : (f.domain : Scheme.{u}) ⟶ (f.toRationalMap.toPartialMap.domain :
      Scheme.{u}) =>
      g ≫ f.toRationalMap.toPartialMap.hom) hfactor).trans key)

theorem extend_over : extend sX sY hval f hf ≫ sY = sX := by
  let _ := isDominant_ι f.domain f.dense_domain.nonempty
  refine ext_of_isDominant f.domain.ι ?_
  rw [reassoc_of% (ι_extend sX sY hval f hf), hf]

end Totalise

end ProperCurveExtension

open ProperCurveExtension in
theorem _root_.AlgebraicGeometry.Scheme.exists_iso_comp_eq_of_isOpenImmersion_of_isProper {K : Type
  u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    [IsIntegral C'] [IsProper c'] [Smooth c']
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (j : (U : Scheme.{u}) ⟶ C') [IsOpenImmersion j] (hj : j ≫ c' = U.ι ≫ c) :
    ∃ e : C ≅ C', e.hom ≫ c' = c ∧ U.ι ≫ e.hom = j := by
  have hvalC : ∀ x : C, ValuationRing (C.presheaf.stalk x) :=
    valuationRing_stalk_of_smoothOfRelativeDimension_one c
  let V : C'.Opens := j.opensRange
  have hV : (V : Set C').Nonempty := ⟨j ⟨_, hU.some_mem⟩, Set.mem_range_self _⟩
  have hVc' : V.ι ≫ c' = j.isoOpensRange.inv ≫ U.ι ≫ c := by
    rw [← hj, Scheme.Hom.isoOpensRange_inv_comp_assoc]
  let _ : SmoothOfRelativeDimension 1 (V.ι ≫ c') := by
    rw [hVc']
    have h : SmoothOfRelativeDimension (0 + (0 + 1)) (j.isoOpensRange.inv ≫ U.ι ≫ c) :=
      inferInstance
    simpa using h
  let _ : SmoothOfRelativeDimension 1 c' := smoothOfRelativeDimension_of_irreducibleSpace 1 c' V hV
  have hvalC' : ∀ y : C', ValuationRing (C'.presheaf.stalk y) :=
    valuationRing_stalk_of_smoothOfRelativeDimension_one c'
  have hUd : Dense (U : Set C) := U.2.dense hU
  have hVd : Dense (V : Set C') := V.2.dense hV
  have hG : (j.isoOpensRange.inv ≫ U.ι) ≫ c = V.ι ≫ c' := by rw [Category.assoc, hVc']
  let fwd : C ⟶ C' := extend c c' hvalC ⟨U, hUd, j⟩ hj
  let bwd : C' ⟶ C := extend c' c hvalC' ⟨V, hVd, j.isoOpensRange.inv ≫ U.ι⟩ hG
  have h₁ : U.ι ≫ fwd = j := ι_extend c c' hvalC ⟨U, hUd, j⟩ hj
  have h₂ : V.ι ≫ bwd = j.isoOpensRange.inv ≫ U.ι :=
    ι_extend c' c hvalC' ⟨V, hVd, j.isoOpensRange.inv ≫ U.ι⟩ hG
  let _ : C.IsSeparated := isSeparated_of_isSeparated_over c
  let _ : C'.IsSeparated := isSeparated_of_isSeparated_over c'
  let _ := isDominant_ι U hU
  let _ := isDominant_ι V hV
  have hfb : fwd ≫ bwd = 𝟙 C := by
    refine ext_of_isDominant U.ι ?_
    rw [Category.comp_id, reassoc_of% h₁, ← j.isoOpensRange_hom_ι, Category.assoc, h₂,
      Iso.hom_inv_id_assoc]
  have hbf : bwd ≫ fwd = 𝟙 C' := by
    refine ext_of_isDominant V.ι ?_
    rw [Category.comp_id, reassoc_of% h₂, h₁, Scheme.Hom.isoOpensRange_inv_comp]
  exact ⟨⟨fwd, bwd, hfb, hbf⟩, extend_over c c' hvalC ⟨U, hUd, j⟩ hj, h₁⟩

end
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper
end ProofImplementation
