/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.CechObstruction
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom

/-!
# Small Extension is Pic Deformation Cocycle unit pullback Unit Iso zero
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs
namespace SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace UnitClassZero

open _root_.AlgebraicGeometry.Scheme.Modules


section coh
variable {T' T : Scheme.{u}}

lemma congr_unit_hom {f f' : T' ⟶ T} (H : f = f') :
    (pullbackCongr H).hom.app (SheafOfModules.unit T.ringCatSheaf) ≫ (pullbackUnitIso f').hom =
      (pullbackUnitIso f).hom := by
  subst H
  exact Category.id_comp (pullbackUnitIso f).hom

lemma congr_unit_inv {f f' : T' ⟶ T} (H : f = f') :
    (pullbackCongr H).inv.app (SheafOfModules.unit T.ringCatSheaf) ≫ (pullbackUnitIso f).hom =
      (pullbackUnitIso f').hom := by
  subst H
  exact Category.id_comp (pullbackUnitIso f).hom

lemma comp_inv_map_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackComp f g).inv.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom =
      (pullbackUnitIso (f ≫ g)).hom := by
  erw [← Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom f g]
  erw [Iso.inv_hom_id_app_assoc]

end coh

variable {X : Scheme.{u}}

/-- The canonical Čech trivialization of the unit module on the ordered affine cover. -/
noncomputable def canTriv (𝒰 : X.OrderedAffineCover) :
    CechTrivialisation 𝒰 (SheafOfModules.unit X.ringCatSheaf) := fun a => pullbackUnitIso (𝒰.U a).ι

lemma canTriv_restrict (𝒰 : X.OrderedAffineCover) {a : 𝒰.ι} {W : X.Opens} (h : W ≤ 𝒰.U a) :
    (canTriv 𝒰).restrict h = pullbackUnitIso W.ι := by
  apply Iso.ext
  change (pullbackCongr (X.homOfLE_ι h)).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (pullbackComp (X.homOfLE h) (𝒰.U a).ι).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pullback (X.homOfLE h)).map (pullbackUnitIso (𝒰.U a).ι).hom ≫
          (pullbackUnitIso (X.homOfLE h)).hom =
    (pullbackUnitIso W.ι).hom
  rw [comp_inv_map_unit]
  exact congr_unit_inv _

lemma uAS_eq_one_of_eq_refl {Y : Scheme.{u}} (W : Y.Opens)
    (e : SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf ≅ SheafOfModules.unit ((W :
      Scheme.{u})).ringCatSheaf)
    (h : e = Iso.refl _) : unitAutSection W e = 1 := by
  subst h
  exact (Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl W).2

lemma uAS_symm_trans {Y : Scheme.{u}} (W : Y.Opens) {A : ((W : Scheme.{u})).Modules}
    (e : A ≅ SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf) :
    unitAutSection W (e.symm ≪≫ e) = 1 :=
  uAS_eq_one_of_eq_refl W _ (Iso.symm_self_id e)

lemma canTriv_transition (𝒰 : X.OrderedAffineCover) (s : 𝒰.Idx 1) : (canTriv 𝒰).transition s = 1 :=
  by
  simp only [CechTrivialisation.transition, canTriv_restrict]
  exact uAS_symm_trans _ _

lemma canTriv_comap (𝒰 : X.OrderedAffineCover) {X₀ : Scheme.{u}} (g : X₀ ⟶ X) [IsAffineHom g] (a :
  𝒰.ι) :
    (canTriv 𝒰).comap g a =
      (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso (pullbackUnitIso g) ≪≫
        pullbackUnitIso ((𝒰.comap g).U a).ι := by
  apply Iso.ext
  change (pullbackComp (g ⁻¹ᵁ 𝒰.U a).ι g).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (pullbackCongr (morphismRestrict_ι g (𝒰.U a)).symm).hom.app (SheafOfModules.unit
        X.ringCatSheaf) ≫
        (pullbackComp (g ∣_ 𝒰.U a) (𝒰.U a).ι).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
          (Scheme.Modules.pullback (g ∣_ 𝒰.U a)).map (pullbackUnitIso (𝒰.U a).ι).hom ≫
            (pullbackUnitIso (g ∣_ 𝒰.U a)).hom =
    (Scheme.Modules.pullback (g ⁻¹ᵁ 𝒰.U a).ι).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso (g ⁻¹ᵁ
      𝒰.U a).ι).hom
  rw [comp_inv_map_unit, congr_unit_hom]
  exact Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom _ _

end UnitClassZero

theorem _root_.AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_unit_pullbackUnitIso_zero
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g] (𝒰 : X.OrderedAffineCover) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 (SheafOfModules.unit X.ringCatSheaf)
      (Scheme.Modules.pullbackUnitIso g) 0 := by
  refine ⟨UnitClassZero.canTriv 𝒰, fun _ => 1, fun _ => 1, fun _ => mul_one 1, fun a => ?_, fun s
    => ?_⟩
  · rw [map_one, UnitClassZero.canTriv_comap]
    exact (UnitClassZero.uAS_symm_trans _ _).symm
  · rw [UnitClassZero.canTriv_transition, map_one, map_one]
    refine ⟨0, fun _ => 0, fun _ => 0, ?_, fun ξ => ?_⟩
    · simp
    · simp only [map_zero, Finset.univ_eq_empty, Finset.sum_empty]
      rfl
end SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero
end AlgebraicCurves.Geometry.Picard.Proofs
end ProofImplementation
