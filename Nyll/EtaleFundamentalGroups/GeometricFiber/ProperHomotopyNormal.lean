/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCoverSteinComparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.HomotopySequenceMaps
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperNormalization
import Nyll.EtaleFundamentalGroups.GaloisCategories.NormalImage
import Nyll.EtaleFundamentalGroups.GaloisCategories.TrivialComposite
import Nyll.SchemeTheory.Morphisms.FiniteEtaleGeometricallyReduced
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Normality of the proper geometric-fibre image

The native Stein comparison identifies a connected cover with a pullback
from the base whenever the cover has a section on one fibre. Over a separably
closed fibre this proves the finite-cover criterion for normality of the
actual image on fundamental groups.
-/

noncomputable section
open CategoryTheory Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A connected finite etale cover with a section on one field-valued fibre
comes from an actual finite etale cover of the base. -/
theorem essImage_pullback_of_connected_fiber_section
    {X S : Scheme.{u}} [ConnectedSpace X]
    (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyReduced f]
    [GeometricallyConnected f] (Y : FiniteEtale X) [IsConnected Y]
    {K : Type u} [Field K] (s : Spec (.of K) ⟶ S)
    (a : Limits.pullback s f ⟶ Y.left)
    (ha : a ≫ Y.hom = Limits.pullback.snd s f) :
    (pullback f).essImage Y := by
  have hY : ConnectedSpace Y.left := connectedSpace_left_of_isConnected Y
  let g : Y.left ⟶ X := Y.hom
  have hg : IsFiniteEtale g := Y.2
  let c : Y.left ⟶ S := g ≫ f
  have hc : GeometricallyReduced c :=
    GeometricallyReduced.comp_of_isFinite_of_etale g f
  obtain ⟨hfinite, hetale⟩ :=
    finite_etale_fromNormalization_of_proper_flat_geometricallyReduced c
  have hb : IsFiniteEtale c.fromNormalization := .mk
  let A : FiniteEtale S := mk c.fromNormalization
  let r : Y.left ⟶ Limits.pullback f c.fromNormalization :=
    Limits.pullback.lift g c.toNormalization c.toNormalization_fromNormalization.symm
  let e := Limits.pullbackSymmetry s f
  have ha' : (e.inv ≫ a) ≫ g = Limits.pullback.fst f s := by
    rw [Category.assoc, ha]
    exact Limits.pullbackSymmetry_inv_comp_snd s f
  have hr : IsIso r := isIso_steinComparison_of_fiber_section f g s (e.inv ≫ a) ha'
  let q : Y.left ≅ ((pullback f).obj A).left :=
    asIso r ≪≫ Limits.pullbackSymmetry f c.fromNormalization
  have hq : q.hom ≫ ((pullback f).obj A).hom = Y.hom := by
    change (r ≫ (Limits.pullbackSymmetry f c.fromNormalization).hom) ≫
      Limits.pullback.snd c.fromNormalization f = g
    rw [Category.assoc, Limits.pullbackSymmetry_hom_comp_snd]
    exact Limits.pullback.lift_fst _ _ _
  let eY : Y ≅ (pullback f).obj A := MorphismProperty.Over.isoMk q hq
  exact ⟨A, ⟨eY.symm⟩⟩

/-- The image of the actual geometric-fibre fundamental group in a proper
flat family with geometrically reduced connected fibres is normal. -/
theorem fundamentalGroupHom_proper_geometricFiber_range_normal
    {X S : Scheme.{u}} [ConnectedSpace S]
    (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyReduced f]
    [GeometricallyConnected f]
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (.of K) ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback s f) :
    (fundamentalGroupHom (Limits.pullback.snd s f) xi).toMonoidHom.range.Normal := by
  have hX : ConnectedSpace X := GeometricallyConnected.connectedSpace f f.isOpenMap
  let p : Limits.pullback s f ⟶ X := Limits.pullback.snd s f
  have hFibre : ConnectedSpace ↥(Limits.pullback s f) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (Limits.pullback.fst s f)
  apply (autHomOfCompIso_range_normal_iff_terminal_decomposition
    (pullback p) (pullbackFiberIso p xi)).2
  intro Y hY hs
  have hConnected : IsConnected Y := hY
  have hIdentity : IsFiniteEtale (𝟙 (Limits.pullback s f)) := .mk
  let T : FiniteEtale (Limits.pullback s f) := mk (𝟙 _)
  let hT : IsTerminal T :=
    MorphismProperty.Over.mkIdTerminal (@IsFiniteEtale : MorphismProperty Scheme.{u}) _
  let eT : T ≅ ⊤_ (FiniteEtale (Limits.pullback s f)) :=
    hT.uniqueUpToIso terminalIsTerminal
  let v : T ⟶ (pullback p).obj Y := eT.hom ≫ hs.some
  let l : Limits.pullback s f ⟶ Limits.pullback Y.hom p := v.left
  let a : Limits.pullback s f ⟶ Y.left := l ≫ Limits.pullback.fst Y.hom p
  have hv : l ≫ Limits.pullback.snd Y.hom p = 𝟙 _ := v.w
  have ha : a ≫ Y.hom = p := by
    change (l ≫ Limits.pullback.fst Y.hom p) ≫ Y.hom = p
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hv, Category.id_comp]
  obtain ⟨A, ⟨eA⟩⟩ := essImage_pullback_of_connected_fiber_section f Y s a ha
  obtain ⟨ι, hfin, ⟨d⟩⟩ :=
    (autHomOfCompIso_comp_eq_one_iff (pullback f) (pullback p)
      (pullbackFiberIso f (xi ≫ p)) (pullbackFiberIso p xi)).1
      (fundamentalGroupHom_geometricFiber_comp_eq_one f s xi) A
  exact ⟨ι, hfin, ⟨d ≪≫ (pullback p).mapIso eA⟩⟩

end AlgebraicGeometry.FiniteEtale
