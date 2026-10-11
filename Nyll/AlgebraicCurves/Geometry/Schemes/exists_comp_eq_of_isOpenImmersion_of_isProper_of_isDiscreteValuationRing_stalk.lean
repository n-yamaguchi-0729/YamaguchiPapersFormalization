/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.Choose

/-!
# exists comp eq of is Open Immersion of is Proper of is Discrete Valuation Ring stalk
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace ExtendDVR
open _root_.AlgebraicGeometry

variable {κ : Type u} [Field κ] {C : Scheme.{u}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of κ))

/-- The morphism from the spectrum of the function field to the integral scheme. -/
abbrev ηK : Spec C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)
omit [IsIntegral C] in
theorem genericPoint_mem_of_isOpen [IrreducibleSpace C] {W : Set C} (hW : IsOpen W) (hne :
  W.Nonempty) :
    genericPoint C ∈ W :=
  ((genericPoint_spec C).mem_open_set_iff hW).mpr (by simpa using hne)

theorem ηK_base (z : Spec C.functionField) : (ηK (C := C)).base z = genericPoint C := by
  let _ : Unique (PrimeSpectrum C.functionField) := inferInstance
  have hz : z = IsLocalRing.closedPoint C.functionField :=
    Subsingleton.elim (α := PrimeSpectrum C.functionField) _ _
  rw [hz]
  exact Scheme.fromSpecStalk_closedPoint

theorem isDominant_of_comp_eq_ηK {V : Scheme.{u}} (j : V ⟶ C) [IsOpenImmersion j]
    (w : Spec C.functionField ⟶ V) (hw : w ≫ j = ηK) : IsDominant w := by
  let pt : Spec C.functionField := IsLocalRing.closedPoint C.functionField
  have hcomp : j.base (w.base pt) = genericPoint C := by
    rw [← Scheme.Hom.comp_apply, hw]; exact ηK_base pt
  refine ⟨dense_iff_inter_open.mpr fun O hO hOne => ?_⟩
  have hjO : IsOpen (j.base '' O) := j.isOpenEmbedding.isOpenMap O hO
  obtain ⟨v, hvO, hv⟩ : genericPoint C ∈ j.base '' O := genericPoint_mem_of_isOpen hjO (hOne.image
    _)
  refine ⟨v, hvO, ⟨pt, j.isOpenEmbedding.injective ?_⟩⟩
  rw [hv, hcomp]

theorem fst_comp_eq_snd_comp {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of κ)) [IsSeparated p]
    {V₁ V₂ : Scheme.{u}} (j₁ : V₁ ⟶ C) (j₂ : V₂ ⟶ C) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (g₁ : V₁ ⟶ P) (g₂ : V₂ ⟶ P) (hg₁ : g₁ ≫ p = j₁ ≫ c) (hg₂ : g₂ ≫ p = j₂ ≫ c)
    (w₁ : Spec C.functionField ⟶ V₁) (w₂ : Spec C.functionField ⟶ V₂)
    (hw₁ : w₁ ≫ j₁ = ηK) (hw₂ : w₂ ≫ j₂ = ηK) (hgw : w₁ ≫ g₁ = w₂ ≫ g₂) :
    pullback.fst j₁ j₂ ≫ g₁ = pullback.snd j₁ j₂ ≫ g₂ := by
  let w : Spec C.functionField ⟶ pullback j₁ j₂ := pullback.lift w₁ w₂ (by rw [hw₁, hw₂])
  let _ : IsDominant w :=
    isDominant_of_comp_eq_ηK (pullback.fst j₁ j₂ ≫ j₁) w (by rw [pullback.lift_fst_assoc, hw₁])
  let _ : IsReduced (pullback j₁ j₂) := isReduced_of_isOpenImmersion (pullback.fst j₁ j₂ ≫ j₁)
  refine ext_of_isDominant_of_isSeparated p ?_ w ?_
  · rw [Category.assoc, hg₁, Category.assoc, hg₂, pullback.condition_assoc]
  · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hgw]

theorem specMap_algebraMap_fromSpecStalk (x : C) :
    Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
      C.fromSpecStalk x = ηK := by
  change Spec.map (CommRingCat.ofHom (C.presheaf.stalkSpecializes _).hom) ≫ _ = _
  rw [CommRingCat.ofHom_hom, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

variable {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of κ))

theorem exists_chart [IsProper p] (t : Spec C.functionField ⟶ P) (ht : t ≫ p = ηK ≫ c)
    (x : C) (hx : IsDiscreteValuationRing (C.presheaf.stalk x)) :
    ∃ (V : C.Opens) (_ : x ∈ V) (g : (V : Scheme.{u}) ⟶ P) (a : Spec C.functionField ⟶ (V :
      Scheme.{u})),
      g ≫ p = V.ι ≫ c ∧ a ≫ V.ι = ηK ∧ a ≫ g = t := by
  let _ := hx
  have hV : ValuativeCriterion p := by
    have h := (inferInstance : IsProper p)
    rw [AlgebraicGeometry.IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
      C.fromSpecStalk x = ηK := specMap_algebraMap_fromSpecStalk x
  have hsq : CommSq t (Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x)
    C.functionField))) p
      (C.fromSpecStalk x ≫ c) := ⟨by rw [ht, ← Category.assoc]; exact (congrArg (· ≫ c) hspec).symm⟩
  let _ : hsq.HasLift :=
    ValuativeCriterion.existence hV (ValuativeCommSq.mk (C.presheaf.stalk x) C.functionField _ _
      hsq)
  let _ : LocallyOfFiniteType p := by
    have h := (inferInstance : IsProper p)
    rw [AlgebraicGeometry.IsProper.eq_valuativeCriterion] at h
    exact h.2
  obtain ⟨V, hxV, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' c p hsq.lift hsq.fac_right
  refine ⟨V, hxV, g, Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField))
    ≫
    V.fromSpecStalkOfMem x hxV, hg₂, ?_, ?_⟩
  · rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]; exact hspec
  · rw [Category.assoc, ← hg₁, hsq.fac_left]

end AlgebraicGeometry.ExtendDVR


end
end exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
universe u


open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk in
open AlgebraicGeometry.ExtendDVR in
theorem exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
    {κ : Type u} [Field κ] {C U P : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of κ)) [IsIntegral C]
    (u : U ⟶ C) [IsOpenImmersion u] [Nonempty U]
    (hreg : ∀ x : C, x ∉ Set.range u.base → IsDiscreteValuationRing (C.presheaf.stalk x))
    (p : P ⟶ Spec (CommRingCat.of κ)) [IsProper p]
    (f : U ⟶ P) (hf : f ≫ p = u ≫ c) :
    ∃ g : C ⟶ P, g ≫ p = c ∧ u ≫ g = f := by
  classical
  have hηmem : ∀ z : Spec C.functionField, (ηK (C := C)).base z ∈ Set.range u.base := by
    intro z
    rw [ηK_base]
    exact genericPoint_mem_of_isOpen u.isOpenEmbedding.isOpen_range (Set.range_nonempty _)
  let ηU : Spec C.functionField ⟶ U := IsOpenImmersion.lift u ηK
    (by rintro _ ⟨z, rfl⟩; exact hηmem z)
  have hηU : ηU ≫ u = ηK := IsOpenImmersion.lift_fac u ηK _
  let ι := {x : C // x ∉ Set.range u.base}
  have hex : ∀ i : ι, ∃ (V : C.Opens) (_ : i.1 ∈ V) (g : (V : Scheme.{u}) ⟶ P) (a : Spec
    C.functionField ⟶ (V : Scheme.{u})),
      g ≫ p = V.ι ≫ c ∧ a ≫ V.ι = ηK ∧ a ≫ g = ηU ≫ f := fun i =>
    exists_chart c p (ηU ≫ f) (by rw [Category.assoc, hf, ← Category.assoc, hηU]) i.1 (hreg i.1 i.2)
  choose V hV g a hg ha hag using hex
  let X : Option ι → Scheme.{u} := fun o => o.elim U (fun i => (V i : Scheme.{u}))
  let j : ∀ o : Option ι, X o ⟶ C := fun o => match o with
    | none => u
    | some i => (V i).ι
  have hj : ∀ o : Option ι, IsOpenImmersion (j o) := by
    rintro (_ | i)
    · change IsOpenImmersion u; infer_instance
    · change IsOpenImmersion (V i).ι; infer_instance
  let _ : ∀ o : Option ι, IsOpenImmersion (j o) := hj
  have hcov : ∀ y : C, ∃ (o : Option ι) (z : X o), (j o).base z = y := by
    intro y
    by_cases hy : y ∈ Set.range u.base
    · obtain ⟨z, hz⟩ := hy
      exact ⟨none, z, hz⟩
    · exact ⟨some ⟨y, hy⟩, ⟨y, hV ⟨y, hy⟩⟩, rfl⟩
  let 𝒰 : C.OpenCover := Scheme.Cover.mkOfCovers (Option ι) X j hcov (fun o => hj o)
  let gl : ∀ o : Option ι, X o ⟶ P := fun o => match o with
    | none => f
    | some i => g i
  have hgl : ∀ o : Option ι, gl o ≫ p = j o ≫ c := by
    rintro (_ | i)
    · exact hf
    · exact hg i
  let w : ∀ o : Option ι, Spec C.functionField ⟶ X o := fun o => match o with
    | none => ηU
    | some i => a i
  have hw : ∀ o : Option ι, w o ≫ j o = ηK := by
    rintro (_ | i)
    · exact hηU
    · exact ha i
  have hwg : ∀ o : Option ι, w o ≫ gl o = ηU ≫ f := by
    rintro (_ | i)
    · rfl
    · exact hag i
  let _ : IsSeparated p := inferInstance
  have hcompat : ∀ o₁ o₂ : Option ι,
      pullback.fst (𝒰.f o₁) (𝒰.f o₂) ≫ gl o₁ = pullback.snd (𝒰.f o₁) (𝒰.f o₂) ≫ gl o₂ := fun o₁ o₂
        =>
    fst_comp_eq_snd_comp c p (j o₁) (j o₂) (gl o₁) (gl o₂) (hgl o₁) (hgl o₂) (w o₁) (w o₂) (hw o₁)
      (hw o₂)
      ((hwg o₁).trans (hwg o₂).symm)
  let glCover : ∀ o : 𝒰.I₀, 𝒰.X o ⟶ P := gl
  have hcompatCover : ∀ o₁ o₂ : 𝒰.I₀,
      pullback.fst (𝒰.f o₁) (𝒰.f o₂) ≫ glCover o₁ =
        pullback.snd (𝒰.f o₁) (𝒰.f o₂) ≫ glCover o₂ := hcompat
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 glCover hcompatCover, ?_, ?_⟩
  · apply Scheme.Cover.hom_ext 𝒰
    intro o
    have hglue : 𝒰.f o ≫ Scheme.Cover.glueMorphisms 𝒰 glCover hcompatCover = glCover o :=
      Scheme.Cover.ι_glueMorphisms 𝒰 glCover hcompatCover o
    exact (Category.assoc (𝒰.f o) (Scheme.Cover.glueMorphisms 𝒰 glCover hcompatCover) p).symm.trans
      ((congrArg (fun k : 𝒰.X o ⟶ P => k ≫ p) hglue).trans (hgl o))
  · exact Scheme.Cover.ι_glueMorphisms 𝒰 glCover hcompatCover none

end AlgebraicGeometry
end ProofImplementation
