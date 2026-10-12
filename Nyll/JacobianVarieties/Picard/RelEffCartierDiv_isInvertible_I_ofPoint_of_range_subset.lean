/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_ofPoint_of_range_subset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_of_forall_comap_openCover
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv

/-!
# Invertibility of the ideal of a point on the smooth locus

The point ideal is invertible after restriction to the smooth open and is the unit ideal
on the complement of the graph. These two descriptions give an invertible ideal globally.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PointIdealInvertibility

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace SectInvAux

/-- The open immersion on the pullbacks induced by an open of the curve. -/
noncomputable def jV {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (V : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : pullback (V.ι ≫ c) t ⟶ pullback c t :=
  pullback.map _ _ _ _ V.ι (𝟙 T) (𝟙 _) (by rw [Category.comp_id])
    (by rw [Category.comp_id, Category.id_comp])

scoped instance {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (V : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : IsOpenImmersion (jV c V t) := by
  dsimp only [jV]; infer_instance

lemma jV_fst {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (V : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    jV c V t ≫ pullback.fst c t = pullback.fst _ _ ≫ V.ι :=
  pullback.lift_fst _ _ _

lemma jV_snd {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (V : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    jV c V t ≫ pullback.snd c t = pullback.snd _ _ ≫ 𝟙 T :=
  pullback.lift_snd _ _ _

lemma isPullback_of_fac {P X Y : Scheme.{u}} (γ' : P ⟶ Y) (j : Y ⟶ X) [Mono j]
    (γ : P ⟶ X) (h : γ' ≫ j = γ) :
    IsPullback γ' (𝟙 P) j γ := by
  refine IsPullback.of_isLimit' ⟨by rw [Category.id_comp, h]⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => Category.comp_id _)
    (fun s m _ hm => ?_)
  · rw [← cancel_mono j, Category.assoc, h]
    exact s.condition.symm
  · simpa only [Category.comp_id] using hm

end SectInvAux

open scoped _root_.JacobianVarieties.Picard.Proofs.PointIdealInvertibility.SectInvAux


open SectInvAux in
theorem _root_.AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_ofPoint_of_range_subset
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (V : C.Opens) [SmoothOfRelativeDimension 1 (V.ι ≫ c)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : T ⟶ C) (ha : a ≫ c = t)
    (hV : Set.range a.base ⊆ (V : Set C)) :
    (RelEffCartierDiv.ofPoint c a ha).I.IsInvertible := by
  classical
  let a' : T ⟶ (V : Scheme.{u}) :=
    IsOpenImmersion.lift V.ι a (by simpa only [Scheme.Opens.range_ι] using hV)
  have ha'ι : a' ≫ V.ι = a := IsOpenImmersion.lift_fac _ _ _
  have ha' : a' ≫ (V.ι ≫ c) = t := by rw [← Category.assoc, ha'ι, ha]
  set X := pullback c t
  set γ := graphOver c a ha with hγ
  set γ' := graphOver (V.ι ≫ c) a' ha' with hγ'
  set j := jV c V t with hj
  have hfac : γ' ≫ j = γ := by
    apply pullback.hom_ext
    · rw [Category.assoc, jV_fst, hγ, graphOver_fst, hγ', graphOver_fst_assoc, ha'ι]
    · rw [Category.assoc, jV_snd, hγ, graphOver_snd, hγ', graphOver_snd_assoc]
  have hI : (RelEffCartierDiv.ofPoint c a ha).I = γ.ker := rfl
  have hPB : IsPullback γ' (𝟙 T) j γ := isPullback_of_fac γ' j γ hfac
  have hA : γ.ker.comap j = γ'.ker := by
    ext U : 2
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.ker_ideal_of_isPullback_of_isOpenImmersion γ γ' (𝟙 T) j hPB U]
  have hAinv : (γ.ker.comap j).IsInvertible := by
    rw [hA]
    exact RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint (V.ι ≫ c) a' ha')
  have hcl : IsClosed (Set.range γ.base) := γ.isClosedEmbedding.isClosed_range
  let W : X.Opens := ⟨(Set.range γ.base)ᶜ, hcl.isOpen_compl⟩
  have hB : γ.ker.comap W.ι = ⊤ := by
    ext U : 2
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_top,
      Pi.top_apply,
      Scheme.Hom.ker_apply]
    have hempty : γ ⁻¹ᵁ (W.ι ''ᵁ (U : (W : Scheme.{u}).Opens)) = ⊥ := by
      ext s
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      rintro ⟨w, -, hw⟩
      exact w.2 ⟨s, hw.symm⟩
    have hsub : Subsingleton Γ(T, γ ⁻¹ᵁ (W.ι ''ᵁ (U : (W : Scheme.{u}).Opens))) := by
      rw [hempty]; infer_instance
    rw [eq_top_iff]
    rintro x -
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact Subsingleton.elim _ _
  have hBinv : (γ.ker.comap W.ι).IsInvertible := by
    rw [hB]
    exact Scheme.IdealSheafData.isInvertible_top
  let obj : Bool → Scheme.{u} := fun b => Bool.rec (W : Scheme.{u}) (pullback (V.ι ≫ c) t) b
  let mp : (b : Bool) → obj b ⟶ X := fun b => Bool.rec (motive := fun b => obj b ⟶ X) W.ι j b
  have hcov : ∀ x : X, ∃ (b : Bool) (y : obj b), (mp b).base y = x := by
    intro x
    by_cases hx : x ∈ Set.range γ.base
    · obtain ⟨s, rfl⟩ := hx
      refine ⟨true, (γ').base s, ?_⟩
      change (γ' ≫ j).base s = γ.base s
      rw [hfac]
    · exact ⟨false, ⟨x, hx⟩, rfl⟩
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool obj mp hcov (fun b => by
    cases b
    · change IsOpenImmersion W.ι; infer_instance
    · change IsOpenImmersion j; infer_instance)
  rw [hI]
  refine Scheme.IdealSheafData.IsInvertible.of_forall_comap_openCover 𝒰 γ.ker fun b => ?_
  cases b
  · exact hBinv
  · exact hAinv
end JacobianVarieties.Picard.Proofs.PointIdealInvertibility
end ProofImplementation
