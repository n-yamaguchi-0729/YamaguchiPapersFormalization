/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperNormalization
import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricallyConnectedSectionDescent
import Nyll.SchemeTheory.Morphisms.FiniteEtaleGeometricallyReduced
import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A connected finite etale cover with a fibre section

A section over one field-valued fibre identifies a connected finite etale
cover with the pullback of its native Stein factor. The section determines
a point of the Stein factor by actual section descent. The connected Stein
fibre over that point makes the comparison have degree one.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

private theorem isIso_of_section_of_connected_source
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsFiniteEtale g]
    [ConnectedSpace Y] [Nonempty X] (a : X ⟶ Y) (ha : a ≫ g = 𝟙 X) :
    IsIso g := by
  have hIdentity : IsFiniteEtale (𝟙 X) := .mk
  have hComp : IsFiniteEtale (a ≫ g) := ha.symm ▸ hIdentity
  have hFiniteEtale : IsFiniteEtale a :=
    MorphismProperty.of_postcomp (@IsFiniteEtale : MorphismProperty Scheme.{u})
      (W' := (@IsFiniteEtale : MorphismProperty Scheme.{u})) a g
      (inferInstance : IsFiniteEtale g) hComp
  have hMono : Mono a := ⟨fun u v huv => by
    have h := congrArg (fun k => k ≫ g) huv
    simpa only [Category.assoc, ha, Category.comp_id] using h⟩
  have hOpen : IsOpenImmersion a := (IsFiniteEtale.mono_iff a).mp hMono |>.1
  have hSurjective : Surjective a := IsFiniteEtale.surjective a
  have hIso : IsIso a := (isIso_iff_isOpenImmersion_and_surjective a).mpr
    ⟨hOpen, hSurjective⟩
  have hCompIso : IsIso (a ≫ g) := ha.symm ▸ (inferInstance : IsIso (𝟙 X))
  exact (isIso_comp_left_iff a g).mp hCompIso

/-- A connected finite etale cover admitting a section over one field-valued
fibre is the actual pullback of its relative normalization over the base. -/
theorem isIso_steinComparison_of_fiber_section
    {Y X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyReduced f]
    [GeometricallyConnected f] (g : Y ⟶ X) [IsFiniteEtale g] [ConnectedSpace Y]
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (a : Limits.pullback f s ⟶ Y) (ha : a ≫ g = Limits.pullback.fst f s) :
    IsIso (Limits.pullback.lift g (g ≫ f).toNormalization
      (g ≫ f).toNormalization_fromNormalization.symm) := by
  let c : Y ⟶ S := g ≫ f
  have hReduced : GeometricallyReduced c :=
    GeometricallyReduced.comp_of_isFinite_of_etale g f
  obtain ⟨hFinite, hEtale⟩ :=
    finite_etale_fromNormalization_of_proper_flat_geometricallyReduced c
  let h : Y ⟶ c.normalization := c.toNormalization
  let b : c.normalization ⟶ S := c.fromNormalization
  have hFactor : h ≫ b = c := c.toNormalization_fromNormalization
  have hB : IsFiniteEtale b := .mk
  have hConnected : GeometricallyConnected h :=
    geometricallyConnected_toNormalization_of_proper_flat_geometricallyReduced c
  have hTConnected : ConnectedSpace c.normalization :=
    h.surjective.connectedSpace h.continuous
  let W : Scheme.{u} := Limits.pullback f b
  let r : Y ⟶ W := Limits.pullback.lift g h hFactor.symm
  have hr₁ : r ≫ Limits.pullback.fst f b = g := Limits.pullback.lift_fst _ _ _
  have hr₂ : r ≫ Limits.pullback.snd f b = h := Limits.pullback.lift_snd _ _ _
  have hRComp : IsFiniteEtale (r ≫ Limits.pullback.fst f b) :=
    hr₁.symm ▸ (inferInstance : IsFiniteEtale g)
  have hR : IsFiniteEtale r :=
    MorphismProperty.of_postcomp (@IsFiniteEtale : MorphismProperty Scheme.{u})
      (W' := (@IsFiniteEtale : MorphismProperty Scheme.{u})) r
      (Limits.pullback.fst f b) (inferInstance : IsFiniteEtale (Limits.pullback.fst f b)) hRComp
  have hWConnected : ConnectedSpace W :=
    GeometricallyConnected.connectedSpace (Limits.pullback.snd f b)
      (Limits.pullback.snd f b).isOpenMap
  let p : Limits.pullback f s ⟶ Spec (CommRingCat.of K) := Limits.pullback.snd f s
  have hXConnected : ConnectedSpace ↥(Limits.pullback f s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton p
  let z : ↥(Limits.pullback f s) :=
    Classical.choice (inferInstance : Nonempty ↥(Limits.pullback f s))
  let Ω := AlgebraicClosure ((Limits.pullback f s).residueField z)
  let xi : Spec (CommRingCat.of Ω) ⟶ Limits.pullback f s :=
    Spec.map (CommRingCat.ofHom (algebraMap ((Limits.pullback f s).residueField z) Ω)) ≫
      (Limits.pullback f s).fromSpecResidueField z
  let Ts : FiniteEtale (Spec (CommRingCat.of K)) :=
    FiniteEtale.mk (Limits.pullback.snd b s)
  have haBase : (a ≫ h) ≫ b = p ≫ s := by
    rw [Category.assoc, hFactor]
    change a ≫ (g ≫ f) = Limits.pullback.snd f s ≫ s
    rw [← Category.assoc, ha, Limits.pullback.condition]
  let aT : Limits.pullback f s ⟶ Ts.left := Limits.pullback.lift (a ≫ h) p haBase
  obtain ⟨t₀, ht₀, hat₀⟩ := exists_section_descent_of_flat_geometricallyConnected
    p xi Ts aT (Limits.pullback.lift_snd _ _ _)
  let tLift : Spec (CommRingCat.of K) ⟶ Limits.pullback b s := t₀
  have htLift : tLift ≫ Limits.pullback.snd b s = 𝟙 (Spec (CommRingCat.of K)) := ht₀
  have haLift : p ≫ tLift = Limits.pullback.lift (a ≫ h) p haBase := hat₀
  let t : Spec (CommRingCat.of K) ⟶ c.normalization := tLift ≫ Limits.pullback.fst b s
  have ht : t ≫ b = s := by
    change (tLift ≫ Limits.pullback.fst b s) ≫ b = s
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
    rw [htLift, Category.id_comp]
  have hat : a ≫ h = p ≫ t := by
    change a ≫ h = p ≫ (tLift ≫ Limits.pullback.fst b s)
    rw [← Category.assoc, haLift]
    exact (Limits.pullback.lift_fst _ _ _).symm
  let k : Limits.pullback f s ⟶ W := Limits.pullback.lift
    (Limits.pullback.fst f s) (p ≫ t) (by
      rw [Category.assoc, ht]
      exact Limits.pullback.condition)
  have hk₁ : k ≫ Limits.pullback.fst f b = Limits.pullback.fst f s :=
    Limits.pullback.lift_fst _ _ _
  have hk₂ : k ≫ Limits.pullback.snd f b = p ≫ t := Limits.pullback.lift_snd _ _ _
  have hBottomOuter : IsPullback (k ≫ Limits.pullback.fst f b) p f (t ≫ b) := by
    rw [hk₁, ht]
    exact IsPullback.of_hasPullback f s
  have hBottom : IsPullback k p (Limits.pullback.snd f b) t :=
    hBottomOuter.of_right hk₂ (IsPullback.of_hasPullback f b)
  let v : Limits.pullback h t ⟶ Y := Limits.pullback.fst h t
  let q : Limits.pullback h t ⟶ Spec (CommRingCat.of K) := Limits.pullback.snd h t
  let j : Limits.pullback h t ⟶ Limits.pullback f s :=
    Limits.pullback.lift (v ≫ g) q (by
      rw [Category.assoc]
      change v ≫ c = q ≫ s
      calc
        v ≫ c = v ≫ (h ≫ b) :=
          congrArg (fun m : Y ⟶ S => v ≫ m) hFactor.symm
        _ = (v ≫ h) ≫ b := (Category.assoc v h b).symm
        _ = (q ≫ t) ≫ b := congrArg
          (fun m : Limits.pullback h t ⟶ c.normalization => m ≫ b)
          (Limits.pullback.condition (f := h) (g := t))
        _ = q ≫ s := (Category.assoc q t b).trans
          (congrArg (fun m : Spec (CommRingCat.of K) ⟶ S => q ≫ m) ht))
  have hj₁ : j ≫ Limits.pullback.fst f s = v ≫ g := Limits.pullback.lift_fst _ _ _
  have hj₂ : j ≫ p = q := Limits.pullback.lift_snd _ _ _
  have hjr : v ≫ r = j ≫ k := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hr₁, Category.assoc, hk₁, hj₁]
    · rw [Category.assoc, hr₂, Category.assoc, hk₂, ← Category.assoc, hj₂]
      exact Limits.pullback.condition
  have hTopOuter : IsPullback v (j ≫ p) (r ≫ Limits.pullback.snd f b) t := by
    rw [hj₂, hr₂]
    exact IsPullback.of_hasPullback h t
  have hTop : IsPullback v j r k := hTopOuter.of_bot hjr hBottom
  have hJ : IsFiniteEtale j :=
    MorphismProperty.of_isPullback (P := @IsFiniteEtale) hTop hR
  have hYtConnected : ConnectedSpace ↥(Limits.pullback h t) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (Limits.pullback.snd h t)
  let a' : Limits.pullback f s ⟶ Limits.pullback h t := Limits.pullback.lift a p hat
  have ha' : a' ≫ j = 𝟙 (Limits.pullback f s) := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hj₁, ← Category.assoc, Limits.pullback.lift_fst,
        ha, Category.id_comp]
    · rw [Category.assoc, hj₂, Limits.pullback.lift_snd, Category.id_comp]
  have hJIso : IsIso j := isIso_of_section_of_connected_source j a' ha'
  have hPullbackIso : IsIso (Limits.pullback.snd r k) := by
    have hCompIso : IsIso (hTop.isoPullback.hom ≫ Limits.pullback.snd r k) :=
      hTop.isoPullback_hom_snd.symm ▸ hJIso
    exact (isIso_comp_left_iff hTop.isoPullback.hom (Limits.pullback.snd r k)).mp hCompIso
  exact IsFiniteEtale.isIso_of_isIso_snd r k

end AlgebraicGeometry.FiniteEtale
