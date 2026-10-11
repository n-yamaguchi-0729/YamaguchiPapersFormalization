/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.StalkObjectSpreading
import Nyll.SchemeTheory.Descent.PunctureIsoSpreading
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Compatible spreading of a finite etale stalk cover

A cover of an actual local spectrum compatible with a cover of a
retrocompact open extends to an open neighborhood with the same overlap
isomorphism. First spread the local cover, then spread the overlap
isomorphism inside an affine neighborhood. The resulting covers and
comparison are transported back through the canonical open-image maps.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryCompatibleCover (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongCompatibleCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongCompatibleCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

/-- A local finite etale cover compatible with the cover of a retrocompact
open spreads to an actual neighborhood, preserving compatibility on its
intersection with that open. -/
theorem exists_compatible_open_cover_fromSpecStalk
    (X : Scheme.{u}) (U : X.Opens) [QuasiCompact U.ι] (x : X)
    (V : FiniteEtale U.toScheme) (W : FiniteEtale (Spec (X.presheaf.stalk x)))
    (a : (pullback (Limits.pullback.fst (X.fromSpecStalk x) U.ι)).obj W ≅
      (pullback (Limits.pullback.snd (X.fromSpecStalk x) U.ι)).obj V) :
    ∃ (N : X.Opens), x ∈ N ∧ ∃ B : FiniteEtale N.toScheme,
      Nonempty
        ((pullback (X.homOfLE (show U ⊓ N ≤ N from inf_le_right))).obj B ≅
          (pullback (X.homOfLE (show U ⊓ N ≤ U from inf_le_left))).obj V) := by
  obtain ⟨N₀, hx₀, B₀, ⟨e₀⟩⟩ := exists_open_model_fromSpecStalk X x W
  obtain ⟨A, hA, hxA, hAN₀⟩ := exists_isAffineOpen_mem_and_subset hx₀
  have : IsAffine A.toScheme := hA
  let xA : A.toScheme := ⟨x, hxA⟩
  let t : A.toScheme ⟶ N₀.toScheme := X.homOfLE hAN₀
  have ht : t ≫ N₀.ι = A.ι := X.homOfLE_ι hAN₀
  let q := X.fromSpecStalk x
  let q₀ := N₀.fromSpecStalkOfMem x hx₀
  let qA := A.toScheme.fromSpecStalk xA
  let r : Spec (A.toScheme.presheaf.stalk xA) ⟶ Spec (X.presheaf.stalk x) :=
    Spec.map (A.ι.stalkMap xA)
  have hr : r ≫ q = qA ≫ A.ι := Scheme.SpecMap_stalkMap_fromSpecStalk A.ι
  let UA : A.toScheme.Opens := A.ι ⁻¹ᵁ U
  have : QuasiCompact UA.ι := MorphismProperty.of_isPullback
    (P := (@QuasiCompact : MorphismProperty Scheme.{u}))
    (isPullback_morphismRestrict A.ι U) (inferInstanceAs (QuasiCompact U.ι))
  let uU : UA.toScheme ⟶ U.toScheme := A.ι ∣_ U
  have huU : uU ≫ U.ι = UA.ι ≫ A.ι := morphismRestrict_ι A.ι U
  let BA : FiniteEtale A.toScheme := (pullback t).obj B₀
  let C : FiniteEtale UA.toScheme := (pullback UA.ι).obj BA
  let VA : FiniteEtale UA.toScheme := (pullback uU).obj V
  let s := Limits.pullback.snd qA UA.ι
  let d := Limits.pullback.fst qA UA.ι ≫ r
  let v := s ≫ uU
  have hkv : d ≫ q = v ≫ U.ι := by
    rw [Category.assoc, hr, ← Category.assoc, Limits.pullback.condition,
      Category.assoc, ← huU, ← Category.assoc]
  let k : Limits.pullback qA UA.ι ⟶ Limits.pullback q U.ι :=
    Limits.pullback.lift d v hkv
  have hdt : d ≫ q₀ = (s ≫ UA.ι) ≫ t := by
    apply (cancel_mono N₀.ι).mp
    simp only [Category.assoc, q₀, Scheme.Opens.fromSpecStalkOfMem_ι, ht]
    change (Limits.pullback.fst qA UA.ι ≫ r) ≫ q = s ≫ UA.ι ≫ A.ι
    rw [Category.assoc, hr, ← Category.assoc, Limits.pullback.condition, Category.assoc]
  let e₁ := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    s UA.ι (s ≫ UA.ι) rfl
  let e₂ := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (s ≫ UA.ι) t (d ≫ q₀) hdt
  let e₃ := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    d q₀ (d ≫ q₀) rfl
  let ed := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    k (Limits.pullback.fst q U.ι) d (Limits.pullback.lift_fst _ _ _).symm
  let ev := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    k (Limits.pullback.snd q U.ι) v (Limits.pullback.lift_snd _ _ _).symm
  let eU := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    s uU v rfl
  let aA : (pullback s).obj C ≅ (pullback s).obj VA :=
    (e₁.app BA).symm ≪≫ (e₂.app B₀).symm ≪≫ e₃.app B₀ ≪≫
      (pullback d).mapIso e₀ ≪≫ ed.app W ≪≫ (pullback k).mapIso a ≪≫
      (ev.app V).symm ≪≫ eU.app V
  obtain ⟨NA, hxNA, b, _⟩ :=
    exists_open_overlap_iso_fromSpecStalk A.toScheme UA xA C VA aA
  let N : X.Opens := A.ι ''ᵁ NA
  have hxN : x ∈ N := ⟨xA, hxNA, rfl⟩
  let e : NA.toScheme ≅ N.toScheme := A.ι.isoImage NA
  let nA : N.toScheme ⟶ A.toScheme := e.inv ≫ NA.ι
  have hnA : nA ≫ A.ι = N.ι := A.ι.isoImage_inv_ι NA
  let B : FiniteEtale N.toScheme := (pullback nA).obj BA
  let O : X.Opens := U ⊓ N
  let dN : O.toScheme ⟶ N.toScheme := X.homOfLE inf_le_right
  let dU : O.toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
  have hRange : Set.range (dN ≫ nA) ⊆ Set.range UA.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change ((dN ≫ nA) ≫ A.ι) z ∈ U
    rw [Category.assoc, hnA, Scheme.homOfLE_ι]
    exact z.property.1
  let cU : O.toScheme ⟶ UA.toScheme := IsOpenImmersion.lift UA.ι (dN ≫ nA) hRange
  have hcU : cU ≫ UA.ι = dN ≫ nA := IsOpenImmersion.lift_fac UA.ι _ hRange
  have hcUU : cU ≫ uU = dU := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, huU, ← Category.assoc, hcU,
      Category.assoc, hnA, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  let cN : O.toScheme ⟶ NA.toScheme := dN ≫ e.inv
  have hcN : cN ≫ NA.ι = cU ≫ UA.ι := by
    rw [hcU, Category.assoc]
  let l : O.toScheme ⟶ Limits.pullback NA.ι UA.ι :=
    Limits.pullback.lift cN cU hcN
  let es := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    l (Limits.pullback.snd NA.ι UA.ι) cU (Limits.pullback.lift_snd _ _ _).symm
  let eN := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    dN nA (dN ≫ nA) rfl
  let eC := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    cU UA.ι (dN ≫ nA) hcU.symm
  let eV := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    cU uU dU hcUU.symm
  exact ⟨N, hxN, B, ⟨(eN.app BA).symm ≪≫ eC.app BA ≪≫ es.app C ≪≫
    (pullback l).mapIso b ≪≫ (es.app VA).symm ≪≫ (eV.app V).symm⟩⟩

end AlgebraicGeometry.FiniteEtale
