/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.InverseLimitModel
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.Topology.Sheaves.Stalks

/-!
# Finite-etale covers spread from an actual stalk

The stalk is the colimit of the rings of sections on open neighborhoods.
Finite-etale inverse-limit descent supplies a cover of the spectrum of one
such ring. Pulling it back by the neighborhood's affinization gives an
actual cover of that neighborhood, retaining the native stalk comparison.

This is the object-spreading step in Stacks 0BPA and 0BQ5. It does not
assume that the base is affine, quasi-compact, or quasi-separated.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryStalkSpreading (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongStalkSpreading
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongStalkSpreading
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

/-- Every finite-etale cover of the actual local spectrum comes from a
finite-etale cover of an open neighborhood, with its literal native
pullback isomorphic to the supplied cover. -/
theorem exists_open_model_fromSpecStalk
    (X : Scheme.{u}) (x : X) (W : FiniteEtale (Spec (X.presheaf.stalk x))) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (V : FiniteEtale U.toScheme),
      Nonempty ((FiniteEtale.pullback (U.fromSpecStalkOfMem x hxU)).obj V ≅ W) := by
  let F : (OpenNhds x)ᵒᵖ ⥤ CommRingCat.{u} :=
    (OpenNhds.inclusion x).op ⋙ X.presheaf
  let D : (OpenNhds x)ᵒᵖᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (colimit.cocone F).op
  have hc : IsLimit c :=
    isLimitOfPreserves Scheme.Spec (colimit.isColimit F).op
  have : ∀ {i j : (OpenNhds x)ᵒᵖᵒᵖ} (h : i ⟶ j), IsAffineHom (D.map h) :=
    fun h ↦ inferInstanceAs (IsAffineHom (Spec.map (F.map h.unop)))
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, CompactSpace (D.obj i) :=
    fun i ↦ inferInstanceAs (CompactSpace (Spec (F.obj i.unop)))
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, QuasiSeparatedSpace (D.obj i) :=
    fun i ↦ inferInstanceAs (QuasiSeparatedSpace (Spec (F.obj i.unop)))
  obtain ⟨i, N, ⟨e⟩⟩ := exists_inverse_limit_model D c hc W
  let U : X.Opens := i.unop.unop.1
  have hxU : x ∈ U := i.unop.unop.2
  let N' : FiniteEtale (Spec Γ(X, U)) := N
  let V : FiniteEtale U.toScheme := (FiniteEtale.pullback U.toSpecΓ).obj N'
  let e' : (FiniteEtale.pullback (Spec.map (X.presheaf.germ U x hxU))).obj N' ≅ W := e
  let E : FiniteEtale.pullback (Spec.map (X.presheaf.germ U x hxU)) ≅
      FiniteEtale.pullback U.toSpecΓ ⋙
        FiniteEtale.pullback (U.fromSpecStalkOfMem x hxU) :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      (U.fromSpecStalkOfMem x hxU) U.toSpecΓ
      (Spec.map (X.presheaf.germ U x hxU))
      (Scheme.Opens.fromSpecStalkOfMem_toSpecΓ U x hxU).symm
  exact ⟨U, hxU, V, ⟨(E.app N').symm ≪≫ e'⟩⟩

end AlgebraicGeometry.FiniteEtale
