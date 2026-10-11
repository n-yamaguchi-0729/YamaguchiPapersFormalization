/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Cover.Open
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_exists_comap_eq_of_openCover
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq

/-!
The relative divisor functor is a sheaf.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_isSheaf_functor

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
namespace SheafProof
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ)

/-- The open cover of the fibre product obtained by pulling back the given base cover. -/
noncomputable def prodCover {T : Scheme.{u}} (g : T ⟶ S) (𝒰 : T.OpenCover) (gi : ∀ i, 𝒰.X i ⟶ S)
    (hgi : ∀ i, 𝒰.f i ≫ g = gi i) : (pullback f g).OpenCover :=
  Scheme.Cover.mkOfCovers 𝒰.I₀ (fun i => pullback f (gi i))
    (fun i => mapOnProdOver f (𝒰.f i) (hgi i))
    (fun z => by
      obtain ⟨y, hy⟩ := 𝒰.covers (pullback.snd f g z)
      obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback
        (isPullback_mapOnProdOver f (𝒰.f _) (hgi _)) z y hy.symm
      exact ⟨_, w, hw⟩)
    (fun i => MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_mapOnProdOver f (𝒰.f i) (hgi i)).flip inferInstance)

@[scoped simp] lemma prodCover_f {T : Scheme.{u}} (g : T ⟶ S) (𝒰 : T.OpenCover) (gi : ∀ i, 𝒰.X i
    ⟶ S)
    (hgi : ∀ i, 𝒰.f i ≫ g = gi i) (i : 𝒰.I₀) :
    (prodCover f g 𝒰 gi hgi).f i = mapOnProdOver f (𝒰.f i) (hgi i) := rfl

open _root_.CategoryTheory.Presieve in
theorem isSheaf : Presieve.IsSheaf Scheme.zariskiTopology (RelEffCartierDiv.functor f r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro T R hR x hx
  obtain ⟨(𝒰 : Scheme.OpenCover T), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hR
  let gi : ∀ i, 𝒰.X i ⟶ S := fun i => (x (𝒰.f i) (.mk i)).1
  let Di : ∀ i, RelEffCartierDiv f r (gi i) := fun i => (x (𝒰.f i) (.mk i)).2
  have hcompat : ∀ {i j : 𝒰.I₀} {V : Scheme.{u}} (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j)
      (hab : a ≫ 𝒰.f i = b ≫ 𝒰.f j),
      (RelEffCartierDiv.functor f r).map a.op (x (𝒰.f i) (.mk i)) =
        (RelEffCartierDiv.functor f r).map b.op (x (𝒰.f j) (.mk j)) :=
    fun a b hab => hx a b (.mk _) (.mk _) hab
  have hgcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ gi i = pullback.snd _ _ ≫ gi j := by
    intro i j
    have := congrArg Sigma.fst (hcompat (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd _ _)
      pullback.condition)
    simpa [functor_map_apply] using this
  let g : T ⟶ S := 𝒰.glueMorphisms gi hgcompat
  have hgi : ∀ i, 𝒰.f i ≫ g = gi i := fun i => 𝒰.ι_glueMorphisms gi hgcompat i
  let 𝒱 := prodCover f g 𝒰 gi hgi
  have hIcompat : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒱.X i) (b : V ⟶ 𝒱.X j),
      a ≫ 𝒱.f i = b ≫ 𝒱.f j → (Di i).I.comap a = (Di j).I.comap b := by
    intro i j V a b hab
    let gi' : V ⟶ 𝒰.X i := a ≫ pullback.snd f (gi i)
    let gj' : V ⟶ 𝒰.X j := b ≫ pullback.snd f (gi j)
    have hab' : gi' ≫ 𝒰.f i = gj' ≫ 𝒰.f j := by
      have hi : 𝒱.f i ≫ pullback.snd f g = pullback.snd f (gi i) ≫ 𝒰.f i :=
        mapOnProdOver_snd f (𝒰.f i) (hgi i)
      have hj : 𝒱.f j ≫ pullback.snd f g = pullback.snd f (gi j) ≫ 𝒰.f j :=
        mapOnProdOver_snd f (𝒰.f j) (hgi j)
      have hi' : (a ≫ 𝒱.f i) ≫ pullback.snd f g = gi' ≫ 𝒰.f i :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun k : 𝒱.X i ⟶ T => a ≫ k) hi).trans (Category.assoc _ _ _).symm)
      have hj' : (b ≫ 𝒱.f j) ≫ pullback.snd f g = gj' ≫ 𝒰.f j :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun k : 𝒱.X j ⟶ T => b ≫ k) hj).trans (Category.assoc _ _ _).symm)
      exact hi'.symm.trans
        ((congrArg (fun k : V ⟶ pullback f g => k ≫ pullback.snd f g) hab).trans hj')
    have hc := hcompat gi' gj' hab'
    rw [functor_map_apply, functor_map_apply] at hc
    have hk : gi' ≫ gi i = gj' ≫ gi j := congrArg Sigma.fst hc
    have hIk : ((Di i).pullbackAlong gi' hk).I = ((Di j).pullbackAlong gj' rfl).I := by
      have h2 := (Sigma.ext_iff.mp hc).2
      exact congrArg RelEffCartierDiv.I
        (eq_of_heq (((Di i).pullbackAlong_heq gi' hk rfl).trans h2))
    have hfst : a ≫ pullback.fst f (gi i) = b ≫ pullback.fst f (gi j) := by
      have hi : 𝒱.f i ≫ pullback.fst f g = pullback.fst f (gi i) :=
        mapOnProdOver_fst f (𝒰.f i) (hgi i)
      have hj : 𝒱.f j ≫ pullback.fst f g = pullback.fst f (gi j) :=
        mapOnProdOver_fst f (𝒰.f j) (hgi j)
      have hi' : (a ≫ 𝒱.f i) ≫ pullback.fst f g = a ≫ pullback.fst f (gi i) :=
        (Category.assoc _ _ _).trans (congrArg (fun k : 𝒱.X i ⟶ 𝒞 => a ≫ k) hi)
      have hj' : (b ≫ 𝒱.f j) ≫ pullback.fst f g = b ≫ pullback.fst f (gi j) :=
        (Category.assoc _ _ _).trans (congrArg (fun k : 𝒱.X j ⟶ 𝒞 => b ≫ k) hj)
      exact hi'.symm.trans
        ((congrArg (fun k : V ⟶ pullback f g => k ≫ pullback.fst f g) hab).trans hj')
    let γ : V ⟶ pullback f (gj' ≫ gi j) := pullback.lift (a ≫ pullback.fst f (gi i)) (𝟙 V)
      (by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun k : pullback f (gi i) ⟶ S => a ≫ k)
            (pullback.condition (f := f) (g := gi i))).trans
            ((Category.assoc _ _ _).symm.trans (hk.trans (Category.id_comp _).symm))))
    have ha : a = γ ≫ mapOnProdOver f gi' hk := by
      apply pullback.hom_ext
      · (simp only [Category.assoc, mapOnProdOver_fst, γ, pullback.lift_fst]; rfl)
      · simp only [Category.assoc, mapOnProdOver_snd]
        have hs : γ ≫ pullback.snd f (gj' ≫ gi j) = 𝟙 V :=
          pullback.lift_snd _ _ _
        exact ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k : V ⟶ V => k ≫ gi') hs).trans
            (Category.id_comp gi'))).symm
    have hb : b = γ ≫ mapOnProdOver f gj' rfl := by
      apply pullback.hom_ext
      · (simp only [Category.assoc, mapOnProdOver_fst, γ, pullback.lift_fst, hfst]; rfl)
      · simp only [Category.assoc, mapOnProdOver_snd]
        have hs : γ ≫ pullback.snd f (gj' ≫ gi j) = 𝟙 V :=
          pullback.lift_snd _ _ _
        exact ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k : V ⟶ V => k ≫ gj') hs).trans
            (Category.id_comp gj'))).symm
    rw [ha, hb, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    change ((Di i).pullbackAlong gi' hk).I.comap γ = ((Di j).pullbackAlong gj' rfl).I.comap γ
    rw [hIk]
  obtain ⟨I₀, hI₀⟩ := Scheme.IdealSheafData.exists_comap_eq_of_openCover 𝒱 (fun i => (Di i).I)
    hIcompat
  let q := I₀.subschemeι ≫ pullback.snd f g
  have Hsq : ∀ i, ∃ (t : (Di i).I.subscheme ⟶ I₀.subscheme),
      IsPullback t ((Di i).I.subschemeι ≫ pullback.snd f (gi i)) q (𝒰.f i) := by
    intro i
    rw [← hI₀ i]
    refine ⟨(I₀.comapIso (𝒱.f i)).hom ≫ pullback.snd _ _, ?_⟩
    have A : IsPullback ((I₀.comap (𝒱.f i)).subschemeι)
        ((I₀.comapIso (𝒱.f i)).hom ≫ pullback.snd _ _) (𝒱.f i) I₀.subschemeι := by
      refine IsPullback.of_iso (IsPullback.of_hasPullback (𝒱.f i) I₀.subschemeι)
        (I₀.comapIso (𝒱.f i)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      · simp [← Scheme.IdealSheafData.comapIso_hom_fst]
      · rw [Iso.symm_hom, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
      · simp
      · simp
    exact A.flip.paste_vert (isPullback_mapOnProdOver f (𝒰.f i) (hgi i))
  have hfin : IsFinite q := by
    let P : MorphismProperty Scheme.{u} := fun {X Y} (h : X ⟶ Y) => IsFinite h
    have hAffine : HasAffineProperty P (affineAnd RingHom.Finite) :=
      (HasAffineProperty.affineAnd_iff P
        RingHom.finite_respectsIso RingHom.finite_localizationPreserves.away
        RingHom.finite_ofLocalizationSpan).mpr (fun {_ _} h => isFinite_iff h)
    have : IsZariskiLocalAtTarget P :=
      (HasAffineProperty.iff.mp hAffine).1
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := P) (f := q) 𝒰).mpr ?_
    intro i
    obtain ⟨t, Hi⟩ := Hsq i
    have := (Di i).isFinite
    dsimp [Scheme.Cover.pullbackHom]
    rw [← Hi.isoPullback_inv_snd]
    change IsFinite (Hi.isoPullback.inv ≫ ((Di i).I.subschemeι ≫ pullback.snd f (gi i)))
    infer_instance
  have hflat : Flat q := by
    let P : MorphismProperty Scheme.{u} := fun {X Y} (h : X ⟶ Y) => Flat h
    have : HasRingHomProperty P RingHom.Flat := inferInstance
    have hAffine : HasAffineProperty P (sourceAffineLocally RingHom.Flat) :=
      HasRingHomProperty.HasAffineProperty (P := P) (Q := RingHom.Flat)
    have : IsZariskiLocalAtTarget P :=
      (HasAffineProperty.iff.mp hAffine).1
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := P) (f := q) 𝒰).mpr ?_
    intro i
    obtain ⟨t, Hi⟩ := Hsq i
    have := (Di i).flat
    dsimp [Scheme.Cover.pullbackHom]
    rw [← Hi.isoPullback_inv_snd]
    change Flat (Hi.isoPullback.inv ≫ ((Di i).I.subschemeι ≫ pullback.snd f (gi i)))
    infer_instance
  have hlfp : LocallyOfFinitePresentation q := by
    let P : MorphismProperty Scheme.{u} := fun {X Y} (h : X ⟶ Y) => LocallyOfFinitePresentation h
    have : HasRingHomProperty P RingHom.FinitePresentation := inferInstance
    have hAffine : HasAffineProperty P (sourceAffineLocally RingHom.FinitePresentation) :=
      HasRingHomProperty.HasAffineProperty (P := P) (Q := RingHom.FinitePresentation)
    have : IsZariskiLocalAtTarget P :=
      (HasAffineProperty.iff.mp hAffine).1
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := P) (f := q) 𝒰).mpr ?_
    intro i
    obtain ⟨t, Hi⟩ := Hsq i
    have := (Di i).locallyOfFinitePresentation
    dsimp [Scheme.Cover.pullbackHom]
    rw [← Hi.isoPullback_inv_snd]
    change LocallyOfFinitePresentation (Hi.isoPullback.inv ≫ ((Di i).I.subschemeι ≫ pullback.snd
      f (gi i)))
    infer_instance
  have hrank : ∀ t : T, q.finrank t = r := by
    intro t
    obtain ⟨y, hy⟩ := 𝒰.covers t
    obtain ⟨tm, Hi⟩ := Hsq (𝒰.idx t)
    have := (Di (𝒰.idx t)).isFinite
    have := (Di (𝒰.idx t)).flat
    rw [← hy, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ Hi y]
    exact (Di _).finrank_eq y
  let D : RelEffCartierDiv f r g := ⟨I₀, hfin, hflat, hlfp, hrank⟩
  have hDi : ∀ i, D.pullbackAlong (𝒰.f i) (hgi i) = Di i := fun i =>
    RelEffCartierDiv.ext (hI₀ i)
  refine ⟨⟨g, D⟩, ?_, ?_⟩
  · rintro Y _ ⟨i⟩
    erw [functor_map_apply]
    change (⟨𝒰.f i ≫ g, D.pullbackAlong (𝒰.f i) rfl⟩ : Σ g, RelEffCartierDiv f r g) = ⟨gi i, Di i⟩
    exact Sigma.ext (hgi i)
      ((D.pullbackAlong_heq (𝒰.f i) rfl (hgi i)).trans (heq_of_eq (hDi i)))
  · rintro ⟨g', D'⟩ hA
    have hA' : ∀ i, (⟨𝒰.f i ≫ g', D'.pullbackAlong (𝒰.f i) rfl⟩ : Σ g, RelEffCartierDiv f r g) =
        ⟨gi i, Di i⟩ := fun i => by
      have := hA (𝒰.f i) (.mk i)
      erw [functor_map_apply] at this
      exact this
    have hg' : g' = g := Scheme.Cover.hom_ext 𝒰 _ _ fun i =>
      (congrArg Sigma.fst (hA' i)).trans (hgi i).symm
    subst hg'
    congr 1
    apply RelEffCartierDiv.ext
    apply Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq 𝒱
    intro i
    have h2 := (Sigma.ext_iff.mp (hA' i)).2
    have hD'i : D'.pullbackAlong (𝒰.f i) (hgi i) = Di i :=
      eq_of_heq ((D'.pullbackAlong_heq (𝒰.f i) (hgi i) rfl).trans h2)
    exact (congrArg RelEffCartierDiv.I hD'i).trans (congrArg RelEffCartierDiv.I (hDi i)).symm

end AlgebraicGeometry.RelEffCartierDiv.SheafProof

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.isSheaf_functor {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (RelEffCartierDiv.functor f r) :=
  AlgebraicGeometry.RelEffCartierDiv.SheafProof.isSheaf f r
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_isSheaf_functor
end ProofImplementation
