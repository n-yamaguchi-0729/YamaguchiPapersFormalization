/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Scheme exists is Open Immersion of function Field iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_exists_isOpenImmersion_of_functionField_iso

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

theorem isOpenImmersion_ι_comp_of_inverse_on_opens {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Y.Opens) (gB : (B : Scheme.{u}) ⟶ X)
    (W : X.Opens) (hWB : W ≤ f ⁻¹ᵁ B) (hb : f.resLE B W hWB ≫ gB = W.ι)
    (W' : Y.Opens) (hW'B : W' ≤ B) (ha : Y.homOfLE hW'B ≫ gB ≫ f = W'.ι) :
    IsOpenImmersion ((W ⊓ f ⁻¹ᵁ W').ι ≫ f) := by
  classical
  set A : X.Opens := W ⊓ f ⁻¹ᵁ W' with hAdef
  have hb' : ∀ x : (W : Scheme.{u}), gB.base (f.resLE B W hWB |>.base x) = x.1 := fun x => by
    have h := congrArg (fun k : (W : Scheme.{u}) ⟶ X => k.base x) hb
    exact (Scheme.Hom.comp_apply (f.resLE B W hWB) gB x).symm.trans h
  have ha' : ∀ y : (W' : Scheme.{u}), f.base (gB.base ((Y.homOfLE hW'B).base y)) = y.1 := fun y =>
    by
    have h := congrArg (fun k : (W' : Scheme.{u}) ⟶ Y => k.base y) ha
    exact (Scheme.Hom.comp_apply gB f ((Y.homOfLE hW'B).base y)).symm.trans
      ((Scheme.Hom.comp_apply (Y.homOfLE hW'B) (gB ≫ f) y).symm.trans h)
  set A' : Y.Opens := W' ⊓ B.ι ''ᵁ (gB ⁻¹ᵁ A) with hA'def
  have hA'B : A' ≤ B := fun y hy => hW'B hy.1
  have hA'W' : A' ≤ W' := fun y hy => hy.1
  have hAA' : A ≤ f ⁻¹ᵁ A' := by
    intro x hx
    have hxW : x ∈ W := hx.1
    have hfxW' : f.base x ∈ W' := hx.2
    refine ⟨hfxW', ?_⟩
    refine ⟨⟨f.base x, hWB hxW⟩, ?_, rfl⟩
    change gB.base ⟨f.base x, hWB hxW⟩ ∈ A
    have h1 : gB.base ((f.resLE B W hWB).base ⟨x, hxW⟩) = x := hb' ⟨x, hxW⟩
    have h2 : (f.resLE B W hWB).base ⟨x, hxW⟩ = ⟨f.base x, hWB hxW⟩ :=
      Subtype.ext (f.coe_resLE_apply hWB ⟨x, hxW⟩)
    rw [← h2, h1]
    exact hx
  have hrange : Set.range ((Y.homOfLE hA'B ≫ gB).base) ⊆ Set.range A.ι.base := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨hyW', b, hb₀, hby⟩ := y.2
    have hb1 : (Y.homOfLE hA'B).base y = b := by
      apply B.ι.isOpenEmbedding.injective
      change (Y.homOfLE hA'B ≫ B.ι).base y = B.ι.base b
      rw [Scheme.homOfLE_ι]
      exact hby.symm
    rw [Scheme.Opens.range_ι]
    change gB.base ((Y.homOfLE hA'B).base y) ∈ A
    rw [hb1]
    exact hb₀
  let fA : (A : Scheme.{u}) ⟶ A' := f.resLE A' A hAA'
  let gA : (A' : Scheme.{u}) ⟶ A := IsOpenImmersion.lift A.ι (Y.homOfLE hA'B ≫ gB) hrange
  have hgA : gA ≫ A.ι = Y.homOfLE hA'B ≫ gB := IsOpenImmersion.lift_fac _ _ _
  have E1 : fA ≫ gA = 𝟙 _ := by
    rw [← cancel_mono A.ι, Category.assoc, hgA, Category.id_comp]
    change f.resLE A' A hAA' ≫ Y.homOfLE hA'B ≫ gB = A.ι
    rw [← Category.assoc, Scheme.Hom.resLE_map]
    have : f.resLE B A (hAA'.trans ((TopologicalSpace.Opens.map f.base).map hA'B.hom).le) =
        X.homOfLE (inf_le_left : A ≤ W) ≫ f.resLE B W hWB := by
      rw [Scheme.Hom.map_resLE]
    rw [this, Category.assoc, hb, Scheme.homOfLE_ι]
  have E2 : gA ≫ fA = 𝟙 _ := by
    rw [← cancel_mono A'.ι, Category.assoc, Category.id_comp]
    change gA ≫ f.resLE A' A hAA' ≫ A'.ι = A'.ι
    rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, hgA]
    rw [show Y.homOfLE hA'B = Y.homOfLE hA'W' ≫ Y.homOfLE hW'B from
      (Scheme.homOfLE_homOfLE Y hA'W' hW'B).symm]
    simp only [Category.assoc]
    rw [ha, Scheme.homOfLE_ι]
  have : IsIso fA := ⟨gA, E1, E2⟩
  have : A.ι ≫ f = fA ≫ A'.ι := (Scheme.Hom.resLE_comp_ι f hAA').symm
  rw [this]
  infer_instance

namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Opens
open _root_.AlgebraicGeometry.Scheme.Opens
end Scheme.Opens
open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Opens in
theorem Scheme.Opens.fromSpecStalk_comp_eq {X Y : Scheme.{u}} (U : X.Opens) {x : X} (hx : x ∈ U)
    {k₁ k₂ : (U : Scheme.{u}) ⟶ Y}
    (h : U.fromSpecStalkOfMem x hx ≫ k₁ = U.fromSpecStalkOfMem x hx ≫ k₂) :
    (U : Scheme.{u}).fromSpecStalk ⟨x, hx⟩ ≫ k₁ = (U : Scheme.{u}).fromSpecStalk ⟨x, hx⟩ ≫ k₂ := by
  let xU : (U : Scheme.{u}) := ⟨x, hx⟩
  let φ : X.presheaf.stalk x ⟶ (U : Scheme.{u}).presheaf.stalk xU := U.ι.stalkMap xU
  have hφ : IsIso φ :=
    ((IsOpenImmersion.iff_isIso_stalkMap (f := U.ι)).mp inferInstance).2 xU
  change Spec.map (inv φ) ≫ ((U : Scheme.{u}).fromSpecStalk xU ≫ k₁) =
    Spec.map (inv φ) ≫ ((U : Scheme.{u}).fromSpecStalk xU ≫ k₂) at h
  exact (cancel_epi (Spec.map (inv φ))).mp h

theorem isOpenImmersion_ι_comp_of_inverse_on_opens' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Y.Opens) (gB : (B : Scheme.{u}) ⟶ X)
    (W₀ : (f ⁻¹ᵁ B : Scheme.{u}).Opens)
    (hb₀ : W₀.ι ≫ f.resLE B (f ⁻¹ᵁ B) le_rfl ≫ gB = W₀.ι ≫ (f ⁻¹ᵁ B).ι)
    (W'₀ : (B : Scheme.{u}).Opens) (ha₀ : W'₀.ι ≫ gB ≫ f = W'₀.ι ≫ B.ι) :
    IsOpenImmersion ((((f ⁻¹ᵁ B).ι ''ᵁ W₀) ⊓ f ⁻¹ᵁ (B.ι ''ᵁ W'₀)).ι ≫ f) := by
  set W : X.Opens := (f ⁻¹ᵁ B).ι ''ᵁ W₀
  set W' : Y.Opens := B.ι ''ᵁ W'₀
  have hWB : W ≤ f ⁻¹ᵁ B :=
    ((f ⁻¹ᵁ B).ι.image_le_opensRange W₀).trans (Scheme.Opens.opensRange_ι _).le
  have hW'B : W' ≤ B := (B.ι.image_le_opensRange W'₀).trans (Scheme.Opens.opensRange_ι _).le
  have hres : f.resLE B W hWB =
      ((f ⁻¹ᵁ B).ι.isoImage W₀).inv ≫ W₀.ι ≫ f.resLE B (f ⁻¹ᵁ B) le_rfl := by
    rw [← cancel_mono B.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    rw [Scheme.Hom.isoImage_inv_ι_assoc]
  have hb : f.resLE B W hWB ≫ gB = W.ι := by
    rw [hres]; simp only [Category.assoc]; rw [hb₀, Scheme.Hom.isoImage_inv_ι]
  have hhom : Y.homOfLE hW'B = (B.ι.isoImage W'₀).inv ≫ W'₀.ι := by
    rw [← cancel_mono B.ι, Scheme.homOfLE_ι, Category.assoc, Scheme.Hom.isoImage_inv_ι]
  have ha : Y.homOfLE hW'B ≫ gB ≫ f = W'.ι := by
    rw [hhom]; simp only [Category.assoc]; rw [ha₀, Scheme.Hom.isoImage_inv_ι]
  exact isOpenImmersion_ι_comp_of_inverse_on_opens f B gB W hWB hb W' hW'B ha

namespace Scheme.Opens
open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Opens in
private theorem _root_.AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_eq_of_eq {X : Scheme.{u}}
  (U : X.Opens) {y y' : X}
    (e : y = y') (hy : y ∈ U) (hy' : y' ∈ U) :
    U.fromSpecStalkOfMem y hy =
      Spec.map (X.presheaf.stalkSpecializes (specializes_of_eq e)) ≫ U.fromSpecStalkOfMem y' hy' :=
        by
  subst e; simp

end Scheme.Opens
open _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Opens in
theorem Scheme.Opens.fromSpecStalkOfMem_resLE {X Y : Scheme.{u}} (k : X ⟶ Y) (U : Y.Opens) (x : X)
    (hx : x ∈ k ⁻¹ᵁ U) :
    (k ⁻¹ᵁ U).fromSpecStalkOfMem x hx ≫ k.resLE U (k ⁻¹ᵁ U) le_rfl =
      Spec.map (k.stalkMap x) ≫ U.fromSpecStalkOfMem (k.base x) hx := by
  apply (cancel_mono U.ι).mp
  calc
    _ = (k ⁻¹ᵁ U).fromSpecStalkOfMem x hx ≫ (k.resLE U (k ⁻¹ᵁ U) le_rfl ≫ U.ι) :=
      Category.assoc _ _ _
    _ = (k ⁻¹ᵁ U).fromSpecStalkOfMem x hx ≫ ((k ⁻¹ᵁ U).ι ≫ k) :=
      congrArg ((k ⁻¹ᵁ U).fromSpecStalkOfMem x hx ≫ ·) (k.resLE_comp_ι le_rfl)
    _ = ((k ⁻¹ᵁ U).fromSpecStalkOfMem x hx ≫ (k ⁻¹ᵁ U).ι) ≫ k :=
      (Category.assoc _ _ _).symm
    _ = X.fromSpecStalk x ≫ k :=
      congrArg (· ≫ k) ((k ⁻¹ᵁ U).fromSpecStalkOfMem_ι x hx)
    _ = Spec.map (k.stalkMap x) ≫ Y.fromSpecStalk (k x) :=
      (Scheme.SpecMap_stalkMap_fromSpecStalk k (x := x)).symm
    _ = Spec.map (k.stalkMap x) ≫ (U.fromSpecStalkOfMem (k x) hx ≫ U.ι) :=
      congrArg (Spec.map (k.stalkMap x) ≫ ·) (U.fromSpecStalkOfMem_ι (k x) hx).symm
    _ = (Spec.map (k.stalkMap x) ≫ U.fromSpecStalkOfMem (k x) hx) ≫ U.ι :=
      (Category.assoc _ _ _).symm

namespace Scheme
open _root_.AlgebraicGeometry.Scheme
end Scheme
open scoped _root_.AlgebraicGeometry.Scheme in
theorem Scheme.b1_main
    {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsIntegral C'] [LocallyOfFiniteType c] [LocallyOfFiniteType c']
    (ψ : C.functionField ≅ C'.functionField)
    (hψ : Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') ≫ c' =
      C.fromSpecStalk (genericPoint C) ≫ c) :
    ∃ (U : C.Opens) (hη : genericPoint C ∈ U) (j : (U : Scheme.{u}) ⟶ C') (_ : IsOpenImmersion j),
      j ≫ c' = U.ι ≫ c ∧
      U.fromSpecStalkOfMem (genericPoint C) hη ≫ j =
        Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') := by
  classical
  let φ₁ : Spec (C.presheaf.stalk (genericPoint C)) ⟶ C' :=
    Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C')
  have h₁ : φ₁ ≫ c' = C.fromSpecStalk (genericPoint C) ≫ c := by
    simpa only [φ₁, Category.assoc] using hψ
  obtain ⟨D, hηD, fh, hf₁, hf₂⟩ : ∃ (D : C.Opens) (hηD : genericPoint C ∈ D) (fh : (D : Scheme.{u})
    ⟶ C'),
      D.fromSpecStalkOfMem (genericPoint C) hηD ≫ fh = φ₁ ∧ fh ≫ c' = D.ι ≫ c :=
    ⟨_, Scheme.PartialMap.mem_domain_ofFromSpecStalk c c' φ₁ h₁, _,
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk c c' φ₁ h₁,
      Scheme.PartialMap.ofFromSpecStalk_comp c c' φ₁ h₁⟩
  have : Nonempty D := ⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))⟩
  have hIsoSM : IsIso (D.ι.stalkMap (⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))) :=
    ((IsOpenImmersion.iff_isIso_stalkMap (f := D.ι)).mp inferInstance).2
      (⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))
  have : IsLocalHom ψ.inv.hom := isLocalHom_of_isIso ψ.inv
  have hDpt : (D.fromSpecStalkOfMem (genericPoint C) hηD)
      (IsLocalRing.closedPoint (C.presheaf.stalk (genericPoint C))) = (⟨genericPoint C, hηD⟩ : (D :
        Scheme.{u})) := by
    apply D.ι.isOpenEmbedding.injective
    let cp : Spec (C.presheaf.stalk (genericPoint C)) :=
      IsLocalRing.closedPoint (C.presheaf.stalk (genericPoint C))
    have h := congrArg (fun k : Spec (C.presheaf.stalk (genericPoint C)) ⟶ C => k cp)
      (D.fromSpecStalkOfMem_ι (genericPoint C) hηD)
    exact (Scheme.Hom.comp_apply (D.fromSpecStalkOfMem (genericPoint C) hηD) D.ι cp).symm.trans
      (h.trans (Scheme.fromSpecStalk_closedPoint (X := C) (x := genericPoint C)))
  have hfη : fh (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) = genericPoint C' := by
    let cp : Spec (C.presheaf.stalk (genericPoint C)) :=
      IsLocalRing.closedPoint (C.presheaf.stalk (genericPoint C))
    have he := congrArg (fun k : Spec (C.presheaf.stalk (genericPoint C)) ⟶ C' => k cp) hf₁
    calc
      _ = fh ((D.fromSpecStalkOfMem (genericPoint C) hηD) cp) := congrArg fh hDpt.symm
      _ = (D.fromSpecStalkOfMem (genericPoint C) hηD ≫ fh) cp :=
        (Scheme.Hom.comp_apply _ _ cp).symm
      _ = φ₁ cp := he
      _ = C'.fromSpecStalk (genericPoint C') (Spec.map ψ.inv cp) :=
        Scheme.Hom.comp_apply _ _ cp
      _ = C'.fromSpecStalk (genericPoint C')
          (IsLocalRing.closedPoint (C'.presheaf.stalk (genericPoint C'))) :=
        congrArg (C'.fromSpecStalk (genericPoint C')) (Spec_closedPoint (f := ψ.inv))
      _ = genericPoint C' := Scheme.fromSpecStalk_closedPoint
  let φ₂ : Spec (C'.presheaf.stalk (genericPoint C')) ⟶ (D : Scheme.{u}) :=
    Spec.map ψ.hom ≫ D.fromSpecStalkOfMem (genericPoint C) hηD
  have h₂ : φ₂ ≫ (D.ι ≫ c) = C'.fromSpecStalk (genericPoint C') ≫ c' := by
    simp only [φ₂, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι_assoc]
    rw [← hψ, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  obtain ⟨B, hη'B, gB, hg₁⟩ : ∃ (B : C'.Opens) (hη'B : genericPoint C' ∈ B)
      (gB : (B : Scheme.{u}) ⟶ D), B.fromSpecStalkOfMem (genericPoint C') hη'B ≫ gB = φ₂ :=
    ⟨_, Scheme.PartialMap.mem_domain_ofFromSpecStalk c' (D.ι ≫ c) φ₂ h₂, _,
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk c' (D.ι ≫ c) φ₂ h₂⟩
  have : Nonempty B := ⟨⟨genericPoint C', hη'B⟩⟩
  have key_a : B.fromSpecStalkOfMem (genericPoint C') hη'B ≫ gB ≫ fh =
      B.fromSpecStalkOfMem (genericPoint C') hη'B ≫ B.ι := by
    rw [← Category.assoc, hg₁, Scheme.Opens.fromSpecStalkOfMem_ι]
    simp only [φ₂, Category.assoc]
    rw [hf₁]
    simp only [φ₁]
    rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  have hGermB : (B : Scheme.{u}).IsGermInjectiveAt
      (⟨genericPoint C', hη'B⟩ : (B : Scheme.{u})) :=
    (isGermInjectiveAt_iff_of_isOpenImmersion (f := B.ι)
      (x := (⟨genericPoint C', hη'B⟩ : (B : Scheme.{u})))).mp inferInstance
  obtain ⟨W'₀, hW'₀, ha₀⟩ := spread_out_unique_of_isGermInjective' (X := (B : Scheme.{u}))
    (x := ⟨genericPoint C', hη'B⟩) (gB ≫ fh) B.ι (Scheme.Opens.fromSpecStalk_comp_eq B hη'B key_a)
  have hηfB : (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) ∈ fh ⁻¹ᵁ B := by
    change fh (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) ∈ B
    rw [hfη]; exact hη'B
  have key_b : Scheme.Opens.fromSpecStalkOfMem (fh ⁻¹ᵁ B) (⟨genericPoint C, hηD⟩ : (D :
    Scheme.{u})) hηfB ≫ fh.resLE B (fh ⁻¹ᵁ B) le_rfl ≫ gB =
      Scheme.Opens.fromSpecStalkOfMem (fh ⁻¹ᵁ B) (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) hηfB ≫
        (fh ⁻¹ᵁ B).ι := by
    have hres := Scheme.Opens.fromSpecStalkOfMem_resLE fh B
      (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) hηfB
    erw [← Category.assoc, hres, Category.assoc,
      B.fromSpecStalkOfMem_eq_of_eq hfη hηfB hη'B, Category.assoc, hg₁]
    simp only [φ₂]
    erw [(fh ⁻¹ᵁ B).fromSpecStalkOfMem_ι
      (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) hηfB]
    have hD : (D : Scheme.{u}).fromSpecStalk (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) =
        Spec.map (D.ι.stalkMap (⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))) ≫ D.fromSpecStalkOfMem
          (genericPoint C) hηD := by
      simp only [Scheme.Opens.fromSpecStalkOfMem]
      have hmap : Spec.map (D.ι.stalkMap (⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))) ≫
          Spec.map (inv (D.ι.stalkMap (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})))) = 𝟙 _ :=
        (Spec.map_comp _ _).symm.trans
          ((congrArg Spec.map (IsIso.inv_hom_id (I := hIsoSM)
            (D.ι.stalkMap (⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))))).trans (Spec.map_id _))
      exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (D : Scheme.{u}).fromSpecStalk
          (⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))) hmap).trans (Category.id_comp _))).symm
    rw [hD]
    simp only [← Spec.map_comp_assoc]
    congr 2
    have hf₁' := hf₁
    rw [Scheme.Opens.fromSpecStalkOfMem] at hf₁'
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk fh (x := (⟨genericPoint C, hηD⟩ :
      (D : Scheme.{u}))),
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq hfη)] at hf₁'
    simp only [φ₁, ← Spec.map_comp_assoc] at hf₁'
    have hinj := Spec.map_injective ((cancel_mono (C'.fromSpecStalk (genericPoint C'))).mp hf₁')
    have hinj' : C'.presheaf.stalkSpecializes (specializes_of_eq hfη) ≫ fh.stalkMap (⟨genericPoint
      C, hηD⟩ : (D : Scheme.{u})) =
        ψ.inv ≫ D.ι.stalkMap (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) :=
      (@IsIso.comp_inv_eq _ _ _ _ _ _ hIsoSM _ _).mp
        (by simp only [Category.assoc] at hinj; exact hinj)
    rw [Category.assoc, hinj']
    exact ψ.hom_inv_id_assoc _
  have : Nonempty (fh ⁻¹ᵁ B) := ⟨⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηfB⟩⟩
  have hGermA : ((fh ⁻¹ᵁ B : (D : Scheme.{u}).Opens) : Scheme.{u}).IsGermInjectiveAt
      (⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηfB⟩ :
        ((fh ⁻¹ᵁ B : (D : Scheme.{u}).Opens) : Scheme.{u})) :=
    (isGermInjectiveAt_iff_of_isOpenImmersion (f := (fh ⁻¹ᵁ B).ι ≫ D.ι)
      (x := (⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηfB⟩ :
        ((fh ⁻¹ᵁ B : (D : Scheme.{u}).Opens) : Scheme.{u})))).mp inferInstance
  obtain ⟨W₀, hW₀, hb₀⟩ := spread_out_unique_of_isGermInjective' (X := ((fh ⁻¹ᵁ B : (D :
    Scheme.{u}).Opens) : Scheme.{u}))
    (x := ⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηfB⟩) (fh.resLE B (fh ⁻¹ᵁ B) le_rfl ≫ gB)
      (fh ⁻¹ᵁ B).ι
    (Scheme.Opens.fromSpecStalk_comp_eq (fh ⁻¹ᵁ B) hηfB key_b)
  have hOI := isOpenImmersion_ι_comp_of_inverse_on_opens' fh B gB W₀ hb₀ W'₀ ha₀
  set A : (D : Scheme.{u}).Opens := ((fh ⁻¹ᵁ B).ι ''ᵁ W₀) ⊓ fh ⁻¹ᵁ (B.ι ''ᵁ W'₀) with hAdef
  have hηA : (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) ∈ A := by
    refine ⟨⟨⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηfB⟩, hW₀, rfl⟩, ?_⟩
    change fh (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) ∈ B.ι ''ᵁ W'₀
    exact ⟨⟨genericPoint C', hη'B⟩, hW'₀, hfη.symm⟩
  refine ⟨D.ι ''ᵁ A, ⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηA, rfl⟩, (D.ι.isoImage A).inv ≫
    A.ι ≫ fh, inferInstance, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [hf₂, Scheme.Hom.isoImage_inv_ι_assoc]
  · have hlift : (D.ι ''ᵁ A).fromSpecStalkOfMem (genericPoint C) ⟨(⟨genericPoint C, hηD⟩ : (D :
      Scheme.{u})), hηA, rfl⟩ ≫
        (D.ι.isoImage A).inv ≫ A.ι = D.fromSpecStalkOfMem (genericPoint C) hηD := by
      rw [← cancel_mono D.ι]
      simp only [Category.assoc, Scheme.Hom.isoImage_inv_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
      exact (D.ι ''ᵁ A).fromSpecStalkOfMem_ι (genericPoint C) _
    rw [← Category.assoc, ← Category.assoc, Category.assoc _ (D.ι.isoImage A).inv, hlift, hf₁]

end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.exists_isOpenImmersion_of_functionField_iso
    {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsIntegral C'] [LocallyOfFiniteType c] [LocallyOfFiniteType c']
    (ψ : C.functionField ≅ C'.functionField)
    (hψ : Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') ≫ c' =
      C.fromSpecStalk (genericPoint C) ≫ c) :
    ∃ (U : C.Opens) (hη : genericPoint C ∈ U) (j : (U : Scheme.{u}) ⟶ C') (_ : IsOpenImmersion j),
      j ≫ c' = U.ι ≫ c ∧
      U.fromSpecStalkOfMem (genericPoint C) hη ≫ j =
        Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') :=
  AlgebraicGeometry.Scheme.b1_main c c' ψ hψ
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_exists_isOpenImmersion_of_functionField_iso
end ProofImplementation
