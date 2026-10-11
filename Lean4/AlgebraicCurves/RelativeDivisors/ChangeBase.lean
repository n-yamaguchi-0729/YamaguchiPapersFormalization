/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Relative divisors after changing the base of the curve

The canonical associativity isomorphism identifies the actual divisor ideals,
their finite flat projections, and their degrees. This is a change of the base
of the curve, in addition to pullback of a divisor along a test scheme.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RelEffCartierDiv

private def transport
    {C S C' S' T : Scheme.{u}} {f : C ⟶ S} {g : T ⟶ S}
    {f' : C' ⟶ S'} {g' : T ⟶ S'} {r : ℕ}
    (D : RelEffCartierDiv f r g) (e : pullback f' g' ≅ pullback f g)
    (he : e.hom ≫ pullback.snd f g = pullback.snd f' g') :
    RelEffCartierDiv f' r g' := by
  let I := D.I.comap e.hom
  let j : I.subscheme ⟶ D.I.subscheme :=
    (D.I.comapIso e.hom).hom ≫ pullback.snd _ _
  have hj : IsPullback j I.subschemeι D.I.subschemeι e.hom := by
    refine (IsPullback.of_iso_pullback ⟨?_⟩ (D.I.comapIso e.hom) ?_ ?_).flip
    · rw [Category.assoc, ← pullback.condition, D.I.comapIso_hom_fst_assoc]
    · exact D.I.comapIso_hom_fst e.hom
    · rfl
  have hs : IsPullback e.hom (pullback.snd f' g') (pullback.snd f g) (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id _).symm⟩
  have hp := hj.paste_vert hs
  have : IsFinite (D.I.subschemeι ≫ pullback.snd f g) := D.isFinite
  have : Flat (D.I.subschemeι ≫ pullback.snd f g) := D.flat
  have : LocallyOfFinitePresentation (D.I.subschemeι ≫ pullback.snd f g) :=
    D.locallyOfFinitePresentation
  refine ⟨I, MorphismProperty.of_isPullback hp inferInstance,
    MorphismProperty.of_isPullback hp inferInstance,
    MorphismProperty.of_isPullback hp inferInstance, ?_⟩
  intro t
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hp t]
  exact D.finrank_eq t

/-- Divisors on a base changed curve are exactly divisors on the original
curve over the composite test map. The ideals are transported by the actual
pullback associativity isomorphism. -/
def changeBaseEquiv {C S S' T : Scheme.{u}}
    (f : C ⟶ S) (s : S' ⟶ S) (g : T ⟶ S') (r : ℕ) :
    RelEffCartierDiv (pullback.snd f s) r g ≃ RelEffCartierDiv f r (g ≫ s) where
  toFun D := transport D (pullbackLeftPullbackSndIso f s g).symm
    (pullbackLeftPullbackSndIso_inv_snd_snd f s g)
  invFun D := transport D (pullbackLeftPullbackSndIso f s g)
    (pullbackLeftPullbackSndIso_hom_snd f s g)
  left_inv D := by
    apply RelEffCartierDiv.ext
    change (D.I.comap (pullbackLeftPullbackSndIso f s g).inv).comap
      (pullbackLeftPullbackSndIso f s g).hom = D.I
    rw [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
  right_inv D := by
    apply RelEffCartierDiv.ext
    change (D.I.comap (pullbackLeftPullbackSndIso f s g).hom).comap
      (pullbackLeftPullbackSndIso f s g).inv = D.I
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]

theorem changeBaseEquiv_ideal {C S S' T : Scheme.{u}}
    (f : C ⟶ S) (s : S' ⟶ S) (g : T ⟶ S') {r : ℕ}
    (D : RelEffCartierDiv (pullback.snd f s) r g) :
    (changeBaseEquiv f s g r D).I =
      D.I.comap (pullbackLeftPullbackSndIso f s g).inv := rfl

theorem changeBaseEquiv_symm_ideal {C S S' T : Scheme.{u}}
    (f : C ⟶ S) (s : S' ⟶ S) (g : T ⟶ S') {r : ℕ}
    (D : RelEffCartierDiv f r (g ≫ s)) :
    ((changeBaseEquiv f s g r).symm D).I =
      D.I.comap (pullbackLeftPullbackSndIso f s g).hom := rfl

private theorem changeBaseIso_map {C S S' T T' : Scheme.{u}}
    (f : C ⟶ S) (s : S' ⟶ S) {g : T ⟶ S'} {g' : T' ⟶ S'}
    (φ : T' ⟶ T) (hφ : φ ≫ g = g') :
    (pullbackLeftPullbackSndIso f s g').hom ≫
        mapOnProdOver f φ ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ s) hφ)) =
      mapOnProdOver (pullback.snd f s) φ hφ ≫
        (pullbackLeftPullbackSndIso f s g).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mapOnProdOver_fst,
      pullbackLeftPullbackSndIso_hom_fst, mapOnProdOver_fst_assoc]
  · simp only [Category.assoc, mapOnProdOver_snd,
      pullbackLeftPullbackSndIso_hom_snd_assoc, pullbackLeftPullbackSndIso_hom_snd]

/-- Changing the base of the curve commutes with actual pullback of divisors
along every test-scheme morphism. -/
theorem changeBaseEquiv_pullbackAlong {C S S' T T' : Scheme.{u}}
    (f : C ⟶ S) (s : S' ⟶ S) {g : T ⟶ S'} {g' : T' ⟶ S'} {r : ℕ}
    (D : RelEffCartierDiv (pullback.snd f s) r g)
    (φ : T' ⟶ T) (hφ : φ ≫ g = g') :
    changeBaseEquiv f s g' r (D.pullbackAlong φ hφ) =
      (changeBaseEquiv f s g r D).pullbackAlong φ
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ s) hφ)) := by
  apply RelEffCartierDiv.ext
  change (D.I.comap (mapOnProdOver (pullback.snd f s) φ hφ)).comap
      (pullbackLeftPullbackSndIso f s g').inv =
    (D.I.comap (pullbackLeftPullbackSndIso f s g).inv).comap (mapOnProdOver f φ _)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  apply (cancel_mono (pullbackLeftPullbackSndIso f s g).hom).1
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← changeBaseIso_map f s φ hφ, Iso.inv_hom_id_assoc]

/-- The actual scalar extension of a family of relative effective divisors. -/
def changeBase {C S Y : Scheme.{u}} {f : C ⟶ S} {y : Y ⟶ S} {r : ℕ}
    (U : RelEffCartierDiv f r y) {S' : Scheme.{u}} (s : S' ⟶ S) :
    RelEffCartierDiv (pullback.snd f s) r (pullback.snd y s) :=
  (changeBaseEquiv f s (pullback.snd y s) r).symm
    (U.pullbackAlong (pullback.fst y s) (pullback.condition))

theorem changeBase_pullbackAlong {C S Y S' T : Scheme.{u}}
    {f : C ⟶ S} {y : Y ⟶ S} {r : ℕ} (U : RelEffCartierDiv f r y)
    (s : S' ⟶ S) {g : T ⟶ S'} (φ : T ⟶ pullback y s)
    (hφ : φ ≫ pullback.snd y s = g) :
    changeBaseEquiv f s g r ((U.changeBase s).pullbackAlong φ hφ) =
      U.pullbackAlong (φ ≫ pullback.fst y s)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, hφ]) := by
  rw [changeBaseEquiv_pullbackAlong]
  change ((changeBaseEquiv f s (pullback.snd y s) r)
    ((changeBaseEquiv f s (pullback.snd y s) r).symm _)).pullbackAlong _ _ = _
  rw [Equiv.apply_symm_apply, pullbackAlong_comp]

/-- Universality is preserved by arbitrary scalar extension, with the
classifying morphism constructed in the actual scheme pullback. -/
theorem IsUniversal.changeBase {C S Y S' : Scheme.{u}}
    {f : C ⟶ S} {y : Y ⟶ S} {r : ℕ} {U : RelEffCartierDiv f r y}
    (hU : U.IsUniversal) (s : S' ⟶ S) : (U.changeBase s).IsUniversal := by
  intro T g D
  let E : RelEffCartierDiv f r (g ≫ s) := changeBaseEquiv f s g r D
  let a : T ⟶ Y := hU.lift E
  let φ : T ⟶ pullback y s := pullback.lift a g (hU.lift_comp E)
  have hφ : φ ≫ pullback.snd y s = g := pullback.lift_snd _ _ _
  have hφfst : φ ≫ pullback.fst y s = a := pullback.lift_fst _ _ _
  have hφD : (U.changeBase s).pullbackAlong φ hφ = D := by
    apply (changeBaseEquiv f s g r).injective
    rw [changeBase_pullbackAlong]
    have h : U.pullbackAlong (φ ≫ pullback.fst y s)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, hφ]) = E := by
      apply RelEffCartierDiv.ext
      change U.I.comap (mapOnProdOver f (φ ≫ pullback.fst y s) _) = E.I
      simp only [hφfst]
      exact congrArg RelEffCartierDiv.I (hU.pullbackAlong_lift E)
    exact h
  refine ⟨⟨φ, hφ⟩, ?_, ?_⟩
  · exact congrArg RelEffCartierDiv.I hφD
  · intro ψ hψ
    have hψD := congrArg (changeBaseEquiv f s g r) hψ.eq_pullbackAlong
    rw [changeBase_pullbackAlong] at hψD
    have hψfst : ψ.1 ≫ pullback.fst y s = a := by
      apply hU.eq_lift (by rw [Category.assoc, pullback.condition, ← Category.assoc, ψ.2])
      exact congrArg RelEffCartierDiv.I hψD.symm
    apply Subtype.ext
    apply pullback.hom_ext
    · exact hψfst.trans hφfst.symm
    · exact ψ.2.trans hφ.symm

/-- The classifier after scalar extension projects to the original classifier
of the same actual divisor. -/
theorem IsUniversal.changeBase_lift_fst {C S Y S' T : Scheme.{u}}
    {f : C ⟶ S} {y : Y ⟶ S} {r : ℕ} {U : RelEffCartierDiv f r y}
    (hU : U.IsUniversal) (s : S' ⟶ S) {g : T ⟶ S'}
    (D : RelEffCartierDiv (pullback.snd f s) r g) :
    (hU.changeBase s).lift D ≫ pullback.fst y s =
      hU.lift (changeBaseEquiv f s g r D) := by
  apply hU.eq_lift
    (by rw [Category.assoc, pullback.condition, ← Category.assoc,
      IsUniversal.lift_comp])
  have h := congrArg (changeBaseEquiv f s g r)
    ((hU.changeBase s).pullbackAlong_lift D)
  rw [changeBase_pullbackAlong] at h
  exact congrArg RelEffCartierDiv.I h

/-- The inverse ideal module defining the divisor line bundle is transported
by the actual pullback associativity isomorphism. -/
theorem changeBaseEquiv_invModule_iso {C S S' T : Scheme.{u}}
    (f : C ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (s : S' ⟶ S) (g : T ⟶ S') {r : ℕ}
    (D : RelEffCartierDiv f r (g ≫ s)) :
    Nonempty ((Scheme.Modules.pullback (pullbackLeftPullbackSndIso f s g).hom).obj
      D.I.invModule ≅ ((changeBaseEquiv f s g r).symm D).I.invModule) := by
  exact D.isInvertible_I.nonempty_pullback_invModule_iso
    (pullbackLeftPullbackSndIso f s g).hom
    ((changeBaseEquiv f s g r).symm D).isInvertible_I

end AlgebraicGeometry.RelEffCartierDiv
