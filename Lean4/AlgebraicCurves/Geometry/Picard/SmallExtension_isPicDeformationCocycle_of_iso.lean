/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.NatTrans
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Picard.CechObstruction

/-!
# Small Extension is Pic Deformation Cocycle of iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs.SmallExtension_isPicDeformationCocycle_of_iso

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace PicDefIso

variable {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 𝓜' : Y.Modules}

/-- The Čech trivialization transported along an isomorphism of modules. -/
noncomputable def transport (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    Scheme.Modules.CechTrivialisation 𝒱 𝓜' :=
  fun a => (Scheme.Modules.pullback (𝒱.U a).ι).mapIso e ≪≫ τ a

theorem transport_restrict (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    (transport e τ).restrict h = (Scheme.Modules.pullback W.ι).mapIso e ≪≫ τ.restrict h := by
  let Z : Scheme.{u} := W
  let U : Scheme.{u} := 𝒱.U a
  let Z₁ : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let U₁ : U.Modules := SheafOfModules.unit U.ringCatSheaf
  let F : Y.Modules ⥤ U.Modules := Scheme.Modules.pullback (𝒱.U a).ι
  let G : U.Modules ⥤ Z.Modules := Scheme.Modules.pullback (Y.homOfLE h)
  let H : Y.Modules ⥤ Z.Modules := Scheme.Modules.pullback W.ι
  let P : Y.Modules ⥤ Z.Modules :=
    Scheme.Modules.pullback (Y.homOfLE h ≫ (𝒱.U a).ι)
  let α : H ⟶ P := (Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).inv
  let β : P ⟶ F ⋙ G := (Scheme.Modules.pullbackComp (Y.homOfLE h) (𝒱.U a).ι).inv
  let t : F.obj 𝓜 ⟶ U₁ := (τ a).hom
  let q : G.obj U₁ ⟶ Z₁ := (Scheme.Modules.pullbackUnitIso (Y.homOfLE h)).hom
  have hproof :
      α.app 𝓜' ≫ β.app 𝓜' ≫ G.map (F.map e.hom ≫ t) ≫ q =
        H.map e.hom ≫ α.app 𝓜 ≫ β.app 𝓜 ≫ G.map t ≫ q := by
    calc
      α.app 𝓜' ≫ β.app 𝓜' ≫ G.map (F.map e.hom ≫ t) ≫ q =
          α.app 𝓜' ≫ β.app 𝓜' ≫ G.map (F.map e.hom) ≫ G.map t ≫ q :=
        congrArg (fun k : G.obj (F.obj 𝓜') ⟶ Z₁ => α.app 𝓜' ≫ β.app 𝓜' ≫ k)
          (G.map_comp_assoc (F.map e.hom) t q)
      _ = α.app 𝓜' ≫ P.map e.hom ≫ β.app 𝓜 ≫ G.map t ≫ q :=
        congrArg (fun k : P.obj 𝓜' ⟶ Z₁ => α.app 𝓜' ≫ k)
          (β.naturality_assoc e.hom (G.map t ≫ q)).symm
      _ = H.map e.hom ≫ α.app 𝓜 ≫ β.app 𝓜 ≫ G.map t ≫ q :=
        (α.naturality_assoc e.hom (β.app 𝓜 ≫ G.map t ≫ q)).symm
  exact Iso.ext hproof

theorem transport_transition (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) (s : 𝒱.Idx 1)
  :
    (transport e τ).transition s = τ.transition s := by
  let Z : Scheme.{u} := 𝒱.inter s
  let Z₁ : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let F : Y.Modules ⥤ Z.Modules := Scheme.Modules.pullback (𝒱.inter s).ι
  let E : F.obj 𝓜' ≅ F.obj 𝓜 := F.mapIso e
  let t₀ : F.obj 𝓜 ≅ Z₁ := τ.restrict (𝒱.inter_le s 0)
  let t₁ : F.obj 𝓜 ≅ Z₁ := τ.restrict (𝒱.inter_le s 1)
  have h₀ : (transport e τ).restrict (𝒱.inter_le s 0) = E ≪≫ t₀ :=
    transport_restrict e τ (𝒱.inter_le s 0)
  have h₁ : (transport e τ).restrict (𝒱.inter_le s 1) = E ≪≫ t₁ :=
    transport_restrict e τ (𝒱.inter_le s 1)
  have hcancel : (E ≪≫ t₀).symm ≪≫ (E ≪≫ t₁) = t₀.symm ≪≫ t₁ :=
    Iso.ext ((Category.assoc t₀.inv E.inv (E.hom ≫ t₁.hom)).trans
      (congrArg (fun k : F.obj 𝓜 ⟶ Z₁ => t₀.inv ≫ k)
        (E.inv_hom_id_assoc t₁.hom)))
  exact congrArg (Scheme.Modules.unitAutSection (𝒱.inter s))
    ((congrArg₂ (fun x y : F.obj 𝓜' ≅ Z₁ => x.symm ≪≫ y) h₀ h₁).trans hcancel)

theorem transport_comap_hom (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    {Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] (a : 𝒱.ι) :
    ((transport e τ).comap h a).hom =
      (Scheme.Modules.pullback h ⋙ Scheme.Modules.pullback (h ⁻¹ᵁ 𝒱.U a).ι).map e.hom ≫ (τ.comap h
        a).hom := by
  let Z : Scheme.{u} := h ⁻¹ᵁ 𝒱.U a
  let U : Scheme.{u} := 𝒱.U a
  let Z₁ : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let U₁ : U.Modules := SheafOfModules.unit U.ringCatSheaf
  let F : Y.Modules ⥤ U.Modules := Scheme.Modules.pullback (𝒱.U a).ι
  let G : U.Modules ⥤ Z.Modules := Scheme.Modules.pullback (h ∣_ 𝒱.U a)
  let H : Y.Modules ⥤ Z.Modules :=
    Scheme.Modules.pullback h ⋙ Scheme.Modules.pullback (h ⁻¹ᵁ 𝒱.U a).ι
  let P : Y.Modules ⥤ Z.Modules := Scheme.Modules.pullback ((h ⁻¹ᵁ 𝒱.U a).ι ≫ h)
  let Q : Y.Modules ⥤ Z.Modules := Scheme.Modules.pullback ((h ∣_ 𝒱.U a) ≫ (𝒱.U a).ι)
  let α : H ⟶ P := (Scheme.Modules.pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).hom
  let β : P ⟶ Q :=
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι h (𝒱.U a)).symm).hom
  let γ : Q ⟶ F ⋙ G := (Scheme.Modules.pullbackComp (h ∣_ 𝒱.U a) (𝒱.U a).ι).inv
  let t : F.obj 𝓜 ⟶ U₁ := (τ a).hom
  let q : G.obj U₁ ⟶ Z₁ := (Scheme.Modules.pullbackUnitIso (h ∣_ 𝒱.U a)).hom
  have hproof :
      α.app 𝓜' ≫ β.app 𝓜' ≫ γ.app 𝓜' ≫ G.map (F.map e.hom ≫ t) ≫ q =
        H.map e.hom ≫ α.app 𝓜 ≫ β.app 𝓜 ≫ γ.app 𝓜 ≫ G.map t ≫ q := by
    calc
      α.app 𝓜' ≫ β.app 𝓜' ≫ γ.app 𝓜' ≫ G.map (F.map e.hom ≫ t) ≫ q =
          α.app 𝓜' ≫ β.app 𝓜' ≫ γ.app 𝓜' ≫ G.map (F.map e.hom) ≫ G.map t ≫ q :=
        congrArg (fun k : G.obj (F.obj 𝓜') ⟶ Z₁ =>
          α.app 𝓜' ≫ β.app 𝓜' ≫ γ.app 𝓜' ≫ k)
          (G.map_comp_assoc (F.map e.hom) t q)
      _ = α.app 𝓜' ≫ β.app 𝓜' ≫ Q.map e.hom ≫ γ.app 𝓜 ≫ G.map t ≫ q :=
        congrArg (fun k : Q.obj 𝓜' ⟶ Z₁ => α.app 𝓜' ≫ β.app 𝓜' ≫ k)
          (γ.naturality_assoc e.hom (G.map t ≫ q)).symm
      _ = α.app 𝓜' ≫ P.map e.hom ≫ β.app 𝓜 ≫ γ.app 𝓜 ≫ G.map t ≫ q :=
        congrArg (fun k : P.obj 𝓜' ⟶ Z₁ => α.app 𝓜' ≫ k)
          (β.naturality_assoc e.hom (γ.app 𝓜 ≫ G.map t ≫ q)).symm
      _ = H.map e.hom ≫ α.app 𝓜 ≫ β.app 𝓜 ≫ γ.app 𝓜 ≫ G.map t ≫ q :=
        (α.naturality_assoc e.hom (β.app 𝓜 ≫ γ.app 𝓜 ≫ G.map t ≫ q)).symm
  exact hproof

theorem transport_comap (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    {Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] (a : 𝒱.ι) :
    (transport e τ).comap h a =
      (Scheme.Modules.pullback ((𝒱.comap h).U a).ι).mapIso ((Scheme.Modules.pullback h).mapIso e)
        ≪≫ τ.comap h a :=
  Iso.ext (transport_comap_hom e τ h a)

end PicDefIso

open PicDefIso in
theorem _root_.AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_iso
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g]
    (𝒰 : X.OrderedAffineCover)
    {M M' : X.Modules} (e : M ≅ M')
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M'
      ((Scheme.Modules.pullback g).mapIso e.symm ≪≫ φ₀) w := by
  obtain ⟨τ, ea, ea', h1, h2, h3⟩ := hw
  refine ⟨transport e.symm τ, ea, ea', h1, fun a => ?_, fun s => ?_⟩
  · let b : (𝒰.comap g).ι := a
    let W : X₀.Opens := (𝒰.comap g).U b
    let Z : Scheme.{u} := W
    let Z₁ : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
    let X₁ : X₀.Modules := SheafOfModules.unit X₀.ringCatSheaf
    let H : X.Modules ⥤ X₀.Modules := Scheme.Modules.pullback g
    let F : X₀.Modules ⥤ Z.Modules := Scheme.Modules.pullback W.ι
    let E : H.obj M' ≅ H.obj M := H.mapIso e.symm
    let p : H.obj M ≅ X₁ := φ₀
    let T : F.obj (H.obj M) ≅ Z₁ := τ.comap g a
    let T' : F.obj (H.obj M') ≅ Z₁ := (transport e.symm τ).comap g a
    let Q : F.obj X₁ ≅ Z₁ := Scheme.Modules.pullbackUnitIso W.ι
    have ht : T' = F.mapIso E ≪≫ T := transport_comap e.symm τ g a
    have hcancel :
        (F.mapIso E ≪≫ T).symm ≪≫ F.mapIso (E ≪≫ p) ≪≫ Q =
          T.symm ≪≫ F.mapIso p ≪≫ Q := by
      apply Iso.ext
      have hproof :
          (T.inv ≫ (F.mapIso E).inv) ≫ F.map (E.hom ≫ p.hom) ≫ Q.hom =
            T.inv ≫ F.map p.hom ≫ Q.hom := by
        calc
          (T.inv ≫ (F.mapIso E).inv) ≫ F.map (E.hom ≫ p.hom) ≫ Q.hom =
              T.inv ≫ (F.mapIso E).inv ≫ F.map (E.hom ≫ p.hom) ≫ Q.hom :=
            Category.assoc T.inv (F.mapIso E).inv (F.map (E.hom ≫ p.hom) ≫ Q.hom)
          _ = T.inv ≫ (F.mapIso E).inv ≫ F.map E.hom ≫ F.map p.hom ≫ Q.hom :=
            congrArg (fun k : F.obj (H.obj M') ⟶ Z₁ => T.inv ≫ (F.mapIso E).inv ≫ k)
              (F.map_comp_assoc E.hom p.hom Q.hom)
          _ = T.inv ≫ F.map p.hom ≫ Q.hom :=
            congrArg (fun k : F.obj (H.obj M) ⟶ Z₁ => T.inv ≫ k)
              ((F.mapIso E).inv_hom_id_assoc (F.map p.hom ≫ Q.hom))
      exact hproof
    have hiso : T'.symm ≪≫ F.mapIso (E ≪≫ p) ≪≫ Q = T.symm ≪≫ F.mapIso p ≪≫ Q :=
      (congrArg (fun t : F.obj (H.obj M') ≅ Z₁ => t.symm ≪≫ F.mapIso (E ≪≫ p) ≪≫ Q)
        ht).trans hcancel
    exact (h2 a).trans (congrArg (Scheme.Modules.unitAutSection W) hiso.symm)
  · rw [transport_transition]
    exact h3 s
end AlgebraicCurves.Geometry.Picard.Proofs.SmallExtension_isPicDeformationCocycle_of_iso
end ProofImplementation
