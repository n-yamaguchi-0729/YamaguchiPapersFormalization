/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.HomotopySequenceMaps

/-!
# Descending an actual finite etale section along connected fibres

Full faithfulness of pullback for a flat finitely presented morphism with
geometrically connected fibres descends an actual map into a finite etale
cover of the base. The construction preserves its equality with the
original map after composition, so it can be used on a chosen fibre
section in the homotopy sequence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- An actual section of a pulled-back finite etale cover descends along
a flat morphism locally of finite presentation with connected geometric fibres. -/
theorem exists_section_descent_of_flat_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (CommRingCat.of Ω) ⟶ X)
    (T : FiniteEtale S) (a : X ⟶ T.left) (ha : a ≫ T.hom = f) :
    ∃ t : S ⟶ T.left, t ≫ T.hom = 𝟙 S ∧ f ≫ t = a := by
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback f) :=
    pullback_preservesLimitsOfShape_pempty f
  obtain ⟨F⟩ := ((autHomOfCompIso_surjective_tfae
    (fiber (xi ≫ f)) (fiber xi) (pullback f) (pullbackFiberIso f xi)).out 1 2).mp
      (fundamentalGroupHom_surjective_of_flat_geometricallyConnected f xi)
  have : IsFiniteEtale (𝟙 S) := .mk
  let I : FiniteEtale S := mk (𝟙 S)
  let v : ((pullback f).obj I).left ⟶ X := Limits.pullback.snd I.hom f
  let m : (pullback f).obj I ⟶ (pullback f).obj T :=
    MorphismProperty.Over.homMk
      (Limits.pullback.lift (v ≫ a) v (by rw [Category.assoc, ha]))
      (Limits.pullback.lift_snd _ _ _)
  let n : I ⟶ T := F.preimage m
  have hn : (pullback f).map n = m := F.map_preimage m
  refine ⟨n.left, MorphismProperty.Over.w n, ?_⟩
  have hnLeft : ((pullback f).map n).left = m.left :=
    (forget X ⋙ Over.forget X).congr_map hn
  have hMap : ((pullback f).map n).left ≫ Limits.pullback.fst T.hom f =
      Limits.pullback.fst I.hom f ≫ n.left := Limits.pullback.lift_fst _ _ _
  have hLift : m.left ≫ Limits.pullback.fst T.hom f = v ≫ a :=
    Limits.pullback.lift_fst _ _ _
  have hLeft : Limits.pullback.fst I.hom f ≫ n.left = v ≫ a :=
    hMap.symm.trans ((congrArg
      (fun z : ((pullback f).obj I).left ⟶ ((pullback f).obj T).left =>
        z ≫ Limits.pullback.fst T.hom f) hnLeft).trans hLift)
  let w : X ⟶ ((pullback f).obj I).left :=
    Limits.pullback.lift f (𝟙 X)
      ((Category.comp_id f).trans (Category.id_comp f).symm)
  have hw₁ : w ≫ Limits.pullback.fst I.hom f = f := Limits.pullback.lift_fst _ _ _
  have hw₂ : w ≫ v = 𝟙 X := Limits.pullback.lift_snd _ _ _
  calc
    f ≫ n.left = (w ≫ Limits.pullback.fst I.hom f) ≫ n.left :=
      congrArg (fun z : X ⟶ S => z ≫ n.left) hw₁.symm
    _ = w ≫ (Limits.pullback.fst I.hom f ≫ n.left) := Category.assoc _ _ _
    _ = w ≫ (v ≫ a) := congrArg
      (fun z : ((pullback f).obj I).left ⟶ T.left => w ≫ z) hLeft
    _ = (w ≫ v) ≫ a := (Category.assoc _ _ _).symm
    _ = a := (congrArg (fun z : X ⟶ X => z ≫ a) hw₂).trans (Category.id_comp a)

end AlgebraicGeometry.FiniteEtale
