/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrum
import Nyll.SchemeTheory.LocalGeometry.GenericComplementPuncture
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Local cover extensions at generic boundary points

At a generic point of an irreducible component of the complement, the
actual overlap of the local spectrum with the open is its puncture. Local
purity therefore supplies an extending cover, retaining an isomorphism on
the original overlap. This is the local input for Stacks `0EY7`.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

local instance finiteEtaleOverCategoryGenericCover (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongGenericCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongGenericCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

/-- Purity at a generic boundary point extends the actual pulled-back cover
over its local spectrum, with the comparison on the original open overlap. -/
theorem exists_stalk_cover_extension_of_generic_complement
    {X : Scheme.{u}} (U : X.Opens)
    (x : genericPoints {z : X // z ∉ U})
    (hpurity : HasPuncturedPurity (X.presheaf.stalk x.1.1))
    (V : FiniteEtale U.toScheme) :
    ∃ W : FiniteEtale (Spec (X.presheaf.stalk x.1.1)),
      Nonempty
        ((pullback (Limits.pullback.fst (X.fromSpecStalk x.1.1) U.ι)).obj W ≅
          (pullback (Limits.pullback.snd (X.fromSpecStalk x.1.1) U.ι)).obj V) := by
  let q := X.fromSpecStalk x.1.1
  let j := Scheme.puncturedSpectrumInclusion (X.presheaf.stalk x.1.1)
  let e := Scheme.genericComplementPuncturedSpectrumPullbackIso U x
  let r := e.inv ≫ Limits.pullback.snd q U.ι
  have hej : Limits.pullback.fst q U.ι = e.hom ≫ j :=
    (Scheme.genericComplementPuncturedSpectrumPullbackIso_hom_inclusion U x).symm
  have her : Limits.pullback.snd q U.ι = e.hom ≫ r := by
    dsimp only [r]
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  obtain ⟨W, ⟨a⟩⟩ := (hasPuncturedPurity_iff _).mp hpurity ((pullback r).obj V)
  let ej : pullback (Limits.pullback.fst q U.ι) ≅ pullback j ⋙ pullback e.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e.hom j (Limits.pullback.fst q U.ι) hej
  let er : pullback (Limits.pullback.snd q U.ι) ≅ pullback r ⋙ pullback e.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e.hom r (Limits.pullback.snd q U.ι) her
  exact ⟨W, ⟨ej.app W ≪≫ (pullback e.hom).mapIso a ≪≫ (er.app V).symm⟩⟩

end AlgebraicGeometry.FiniteEtale
