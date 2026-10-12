/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Mathlib.Util.WithWeakNamespace

/-!
# Relative effective divisors and the identity base change
-/


section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.IdentityCartierBaseChange

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace RecbDiv

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem isPullback_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (m : X ⟶ Y) :
    IsPullback ((I.comapIso m).hom ≫ pullback.snd m I.subschemeι)
      (I.comap m).subschemeι I.subschemeι m := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso m) ?_ ?_).flip
  · simp only [Scheme.IdealSheafData.comapIso_hom_snd,
      Scheme.IdealSheafData.subschemeMap_subschemeι]
  · exact I.comapIso_hom_fst m
  · rfl

theorem main {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) (g : T ⟶ S) (r : ℕ) :
    (∀ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T),
        ∃ D : RelEffCartierDiv f r g, D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T)) = D'.I) ∧
    (∀ D : RelEffCartierDiv f r g,
        ∃ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T),
          D'.I = D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T))) := by
  set p := pullback.snd f g with hp
  set e : pullback p (𝟙 T) ⟶ pullback f g := pullback.fst p (𝟙 T) with he
  have sqe : IsPullback e (pullback.snd p (𝟙 T)) p (𝟙 T) := IsPullback.of_hasPullback p (𝟙 T)
  refine ⟨fun D' => ?_, fun D => ?_⟩
  · let e' : pullback f g ⟶ pullback p (𝟙 T) := inv e
    have hcomm : e' ≫ pullback.snd p (𝟙 T) = p ≫ 𝟙 T := by
      rw [Category.comp_id]
      have : e ≫ p = pullback.snd p (𝟙 T) ≫ 𝟙 T := pullback.condition
      rw [Category.comp_id] at this
      rw [← this, IsIso.inv_hom_id_assoc]
    have sqe' : IsPullback e' p (pullback.snd p (𝟙 T)) (𝟙 T) :=
      IsPullback.of_horiz_isIso ⟨hcomm⟩
    have sq := (isPullback_comap D'.I e').paste_vert sqe'
    have hfinite := D'.isFinite
    have hflat := D'.flat
    have hlfp := D'.locallyOfFinitePresentation
    refine ⟨{ I := D'.I.comap e'
              isFinite := MorphismProperty.of_isPullback sq hfinite
              flat := MorphismProperty.of_isPullback sq hflat
              locallyOfFinitePresentation := MorphismProperty.of_isPullback sq hlfp
              finrank_eq := fun t => by
                rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq t]
                exact D'.finrank_eq _ }, ?_⟩
    change (D'.I.comap e').comap e = D'.I
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  · have sq := (isPullback_comap D.I e).paste_vert sqe
    have hfinite := D.isFinite
    have hflat := D.flat
    have hlfp := D.locallyOfFinitePresentation
    exact ⟨{ I := D.I.comap e
             isFinite := MorphismProperty.of_isPullback sq hfinite
             flat := MorphismProperty.of_isPullback sq hflat
             locallyOfFinitePresentation := MorphismProperty.of_isPullback sq hlfp
             finrank_eq := fun t => by
               rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq t]
               exact D.finrank_eq _ }, rfl⟩

end RecbDiv

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
with_weak_namespace _root_.AlgebraicGeometry.RelEffCartierDiv
theorem forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst
    {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) (g : T ⟶ S) (r : ℕ) :
    (∀ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T),
        ∃ D : RelEffCartierDiv f r g, D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T)) = D'.I) ∧
    (∀ D : RelEffCartierDiv f r g,
        ∃ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T),
          D'.I = D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T))) :=
  _root_.JacobianVarieties.Picard.Proofs.IdentityCartierBaseChange.RecbDiv.main f g r
end JacobianVarieties.Picard.Proofs.IdentityCartierBaseChange
end ProofImplementation
