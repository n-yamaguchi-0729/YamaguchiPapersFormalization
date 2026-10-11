/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.PushforwardStalkComparison
import SchemeTheory.Etale.FiniteGeometricPoints
import SchemeTheory.Etale.FiniteNeighborhoodSection
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Topology.Sets.Opens

/-!
# Injectivity of the finite direct-image stalk comparison

Equality of two étale sheaf sections is detected on an open subset of the
underlying scheme. Closedness of a finite morphism then shrinks an ambient
neighborhood around the whole fiber. This supplies the injective half of
the finite direct-image stalk formula without assuming any local splitting.
The argument applies to concrete coefficient categories whose forgetful functor
preserves filtered colimits and sheaves, including sets and modules.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace EtaleCohomology

variable {A : Type (u + 1)} [Category.{u} A]
  {FA : A → A → Type u} {CA : A → Type u}
  [∀ M N, FunLike (FA M N) (CA M) (CA N)] [ConcreteCategory.{u} A FA]

private theorem exists_sectionEquality_open
    {Y : Scheme.{u}} [Y.smallEtaleTopology.HasSheafCompose (forget A)]
    (F : Sheaf Y.smallEtaleTopology A)
    (U : Y.Etale) (a b : ToType (F.obj.obj (op U))) :
    ∃ W : U.left.Opens,
      (∀ (V : Y.Etale) (g : V ⟶ U), F.obj.map g.op a = F.obj.map g.op b →
        Set.range g.left ⊆ (W : Set U.left)) ∧
      F.obj.map (MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl :
        (Scheme.Etale.mk (W.ι ≫ U.hom) : Y.Etale) ⟶ U).op a =
      F.obj.map (MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl :
        (Scheme.Etale.mk (W.ι ≫ U.hom) : Y.Etale) ⟶ U).op b := by
  let I := Σ V : Y.Etale, {g : V ⟶ U // F.obj.map g.op a = F.obj.map g.op b}
  let image (i : I) : U.left.Opens :=
    ⟨Set.range i.2.val.left, i.2.val.left.isOpenMap.isOpen_range⟩
  let W : U.left.Opens := ⨆ i : I, image i
  let O : Y.Etale := Scheme.Etale.mk (W.ι ≫ U.hom)
  let j : O ⟶ U := MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
  have hRange (i : I) : Set.range i.2.val.left ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    intro x hx
    exact Opens.mem_iSup.mpr ⟨i, hx⟩
  let l (i : I) : i.1.left ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι i.2.val.left (hRange i)
  have hl (i : I) : l i ≫ W.ι = i.2.val.left :=
    IsOpenImmersion.lift_fac W.ι i.2.val.left (hRange i)
  let k (i : I) : i.1 ⟶ O := MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) (l i) (by
    change l i ≫ (W.ι ≫ U.hom) = i.1.hom
    rw [← Category.assoc, hl]
    exact i.2.val.w)
  have hkj (i : I) : k i ≫ j = i.2.val := by
    apply MorphismProperty.Over.Hom.ext
    exact hl i
  have hCover : Sieve.ofArrows (fun i : I => i.1) k ∈ Y.smallEtaleTopology O := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff k).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, v, hv⟩ := Opens.mem_iSup.mp x.property
    refine Set.mem_iUnion.mpr ⟨i, v, ?_⟩
    apply Subtype.ext
    exact ((Scheme.Hom.comp_apply (l i) W.ι v).symm.trans
      (congrArg (fun f : i.1.left ⟶ U.left => f v) (hl i))).trans hv
  refine ⟨W, ?_, ?_⟩
  · intro V g hg x hx
    exact Opens.mem_iSup.mpr ⟨⟨V, g, hg⟩, hx⟩
  · change F.obj.map j.op a = F.obj.map j.op b
    apply F.isSeparated O (Sieve.ofArrows (fun i : I => i.1) k) hCover
    intro T m hm
    obtain ⟨i, d, rfl⟩ := (Sieve.mem_ofArrows_iff (fun i : I => i.1) k m).mp hm
    have hi : F.obj.map (k i).op (F.obj.map j.op a) =
        F.obj.map (k i).op (F.obj.map j.op b) := by
      rw [← F.obj.map_comp_apply, ← F.obj.map_comp_apply, ← op_comp, hkj]
      exact i.2.property
    rw [op_comp, F.obj.map_comp_apply, F.obj.map_comp_apply, hi]

variable [HasColimitsOfSize.{u, u} A]
  [PreservesFilteredColimitsOfSize.{u, u} (forget A)]

/-- The geometric stalks above an algebraically closed point jointly detect
a direct-image germ for a finite morphism. -/
theorem etalePushforwardStalkComponents_jointly_injective
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    [Y.smallEtaleTopology.HasSheafCompose (forget A)]
    (F : Sheaf Y.smallEtaleTopology A)
    {a b : ToType ((Scheme.pointSmallEtale t).sheafFiber.obj
      (((etaleBaseChange q).sheafPushforwardContinuous A
        X.smallEtaleTopology Y.smallEtaleTopology).obj F))}
    (hab : ∀ s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t},
      etalePushforwardStalkComponent q t s F a =
        etalePushforwardStalkComponent q t s F b) : a = b := by
  obtain ⟨U, u, a, b, rfl, rfl⟩ :=
    (Scheme.pointSmallEtale t).toPresheafFiber_jointly_surjective₂ a b
  let B : Y.Etale := (etaleBaseChange q).obj U
  change ToType (F.obj.obj (op B)) at a b
  change (Over.mk t ⟶ Over.mk U.hom) at u
  let p : B.left ⟶ U.left := pullback.fst U.hom q
  let bq : B.left ⟶ Y := pullback.snd U.hom q
  have hpq : p ≫ U.hom = bq ≫ q := pullback.condition
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.fst U.hom q))
  let u₀ : Spec (CommRingCat.of Ω) ⟶ U.left := u.left
  obtain ⟨W, hW, hWab⟩ := exists_sectionEquality_open F B a b
  have hFiber : ∀ y : B.left, p y = u₀ default → y ∈ W := by
    intro y hy
    obtain ⟨v, hv, hvy⟩ := p.exists_geometricLift_of_isFinite u₀ y hy
    let s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t} :=
      ⟨v ≫ bq, by
        rw [Category.assoc, ← hpq, ← Category.assoc]
        exact (congrArg (fun k => k ≫ U.hom) hv).trans u.w⟩
    have hLift : (etalePushforwardGeometricLift q t s U u).left = v := by
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans hv.symm
      · exact pullback.lift_snd _ _ _
    let P : X.Etaleᵒᵖ ⥤ A := (((etaleBaseChange q).sheafPushforwardContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).obj F).obj
    let γ : F.obj.obj (op B) ⟶ (Scheme.pointSmallEtale t).presheafFiber.obj P :=
      (Scheme.pointSmallEtale t).toPresheafFiber U u P
    let c : (Scheme.pointSmallEtale t).presheafFiber.obj P ⟶
        (Scheme.pointSmallEtale s.val).presheafFiber.obj F.obj :=
      etalePushforwardStalkComponent q t s F
    have hg (z : ToType (F.obj.obj (op B))) : c (γ z) =
        (Scheme.pointSmallEtale s.val).toPresheafFiber B
          (etalePushforwardGeometricLift q t s U u) F.obj z :=
      (ConcreteCategory.comp_apply γ c z).symm.trans
        (ConcreteCategory.congr_hom
          (toPresheafFiber_etalePushforwardStalkComponent q t s F U u) z)
    have hgerm : (Scheme.pointSmallEtale s.val).toPresheafFiber B
        (etalePushforwardGeometricLift q t s U u) F.obj a =
      (Scheme.pointSmallEtale s.val).toPresheafFiber B
        (etalePushforwardGeometricLift q t s U u) F.obj b :=
      (hg a).symm.trans ((hab s).trans (hg b))
    obtain ⟨V, g, w, hw, heq⟩ :=
      ((Scheme.pointSmallEtale s.val).toPresheafFiber_eq_iff' (P := F.obj) B
        (etalePushforwardGeometricLift q t s U u) a b).mp hgerm
    have hwleft : w.left ≫ g.left = v :=
      (congrArg (fun k : Over.mk s.val ⟶ Over.mk B.hom => k.left) hw).trans hLift
    have hwy : g.left (w.left (default : Spec (CommRingCat.of Ω))) = y :=
      (Scheme.Hom.comp_apply w.left g.left (default : Spec (CommRingCat.of Ω))).symm.trans
        ((congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ B.left => k default) hwleft).trans hvy)
    rw [← hwy]
    exact hW V g heq ⟨w.left (default : Spec (CommRingCat.of Ω)), rfl⟩
  obtain ⟨V, hV, hVW⟩ := p.exists_preimage_le_of_fiber_subset (u₀ default) W hFiber
  have huRange : Set.range u₀ ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    exact hV
  let v : Spec (CommRingCat.of Ω) ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι u₀ huRange
  have hv : v ≫ V.ι = u₀ := IsOpenImmersion.lift_fac V.ι u₀ huRange
  let T : X.Etale := Scheme.Etale.mk (V.ι ≫ U.hom)
  let g : T ⟶ U := MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) V.ι rfl
  let w : (Scheme.pointSmallEtale t).fiber.obj T := Over.homMk v (by
    change v ≫ (V.ι ≫ U.hom) = t
    rw [← Category.assoc, hv]
    exact u.w)
  have hw : (Scheme.pointSmallEtale t).fiber.map g w = u := by
    apply Over.OverMorphism.ext
    exact hv
  let m : ((etaleBaseChange q).obj T).left ⟶ B.left :=
    ((etaleBaseChange q).map g).left
  let pT : ((etaleBaseChange q).obj T).left ⟶ V.toScheme := pullback.fst T.hom q
  have hmp : m ≫ p = pT ≫ V.ι := pullback.lift_fst _ _ _
  have hmRange : Set.range m ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨z, rfl⟩
    apply hVW
    change p (m z) ∈ V
    rw [← Scheme.Hom.comp_apply, hmp, Scheme.Hom.comp_apply]
    exact (pT z).property
  let l : ((etaleBaseChange q).obj T).left ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι m hmRange
  have hl : l ≫ W.ι = m := IsOpenImmersion.lift_fac W.ι m hmRange
  let O : Y.Etale := Scheme.Etale.mk (W.ι ≫ B.hom)
  let j : O ⟶ B := MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
  let k : (etaleBaseChange q).obj T ⟶ O := MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) l (by
    change l ≫ (W.ι ≫ B.hom) = ((etaleBaseChange q).obj T).hom
    rw [← Category.assoc, hl]
    exact ((etaleBaseChange q).map g).w)
  have hkj : k ≫ j = (etaleBaseChange q).map g := by
    apply MorphismProperty.Over.Hom.ext
    exact hl
  apply ((Scheme.pointSmallEtale t).toPresheafFiber_eq_iff'
    (P := (((etaleBaseChange q).sheafPushforwardContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).obj F).obj) U u a b).mpr
  refine ⟨T, g, w, hw, ?_⟩
  change F.obj.map ((etaleBaseChange q).map g).op a =
    F.obj.map ((etaleBaseChange q).map g).op b
  rw [← hkj, op_comp, F.obj.map_comp_apply, F.obj.map_comp_apply]
  exact congrArg (F.obj.map k.op) hWab

variable [HasProducts.{u} A]

/-- The canonical product comparison for a finite morphism is a monomorphism
at each algebraically closed geometric point. -/
theorem etalePushforwardStalkComparison_mono
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    [Y.smallEtaleTopology.HasSheafCompose (forget A)]
    (F : Sheaf Y.smallEtaleTopology A) :
    Mono (etalePushforwardStalkComparison q t F) := by
  apply ConcreteCategory.mono_of_injective
  intro a b hab
  apply etalePushforwardStalkComponents_jointly_injective q t F
  intro s
  have h := congrArg
    (Pi.π (fun s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t} =>
      (Scheme.pointSmallEtale s.val).sheafFiber.obj F) s) hab
  have ha := ConcreteCategory.congr_hom (etalePushforwardStalkComparison_π q t s F) a
  have hb := ConcreteCategory.congr_hom (etalePushforwardStalkComparison_π q t s F) b
  simp only [ConcreteCategory.comp_apply] at ha hb
  exact ha.symm.trans (h.trans hb)

end EtaleCohomology
