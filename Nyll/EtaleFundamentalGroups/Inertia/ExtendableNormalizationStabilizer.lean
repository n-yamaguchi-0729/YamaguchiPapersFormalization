/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationBaseChange
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import Nyll.EtaleFundamentalGroups.GaloisCategories.Surjectivity
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Extendable covers have trivial normalized-point stabilizers

Surjectivity on fundamental groups makes restriction fully faithful. A deck
transformation therefore extends to the given finite etale cover. The
normalization maps canonically to that extension, compatibly with the deck
maps. Fixing a normalized geometric point fixes an actual point of the
connected extension, so the deck transformation is the identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem connected_of_connected_pullback
    {U X : Scheme.{u}} [ConnectedSpace U] [ConnectedSpace X]
    (j : U ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ U) (V : FiniteEtale X)
    [IsConnected ((FiniteEtale.pullback j).obj V)] : IsConnected V := by
  let F := fiber (xi ≫ j)
  let F' := fiber xi
  let t := pullbackFiberIso j xi
  let : Nonempty (F.obj V) := ⟨(t.app V).hom
    (Classical.choice (nonempty_fiber_of_isConnected F' ((FiniteEtale.pullback j).obj V)))⟩
  let : MulAction.IsPretransitive (Aut F) (F.obj V) := ⟨by
    intro a b
    let a' : F'.obj ((FiniteEtale.pullback j).obj V) := (t.app V).inv a
    let b' : F'.obj ((FiniteEtale.pullback j).obj V) := (t.app V).inv b
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F') a' b'
    refine ⟨fundamentalGroupHom j xi g, ?_⟩
    have h := (pullbackFiberIso_hom_fundamentalGroupHom_apply j xi g V
      ((t.app V).inv a)).symm.trans (congrArg (t.app V).hom hg)
    change (fundamentalGroupHom j xi g).hom.app V
      ((t.app V).hom ((t.app V).inv a)) = (t.app V).hom ((t.app V).inv b) at h
    change (fundamentalGroupHom j xi g).hom.app V a = b
    simpa only [FintypeCat.inv_hom_id_apply] using h⟩
  exact FiberFunctor.isConnected_of_isPretransitive F V

/-- An actual finite etale extension forces every geometric-point stabilizer
of the relative normalization to be trivial. The extension of deck maps is
constructed from the surjectivity of the induced fundamental-group map. -/
theorem aut_eq_one_of_fixes_normalizationPoint_of_extension
    {U X : Scheme.{u}} [ConnectedSpace U] [ConnectedSpace X]
    (j : U ⟶ X) [QuasiCompact j] [QuasiSeparated j]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ U)
    (hsurj : Function.Surjective (fundamentalGroupHom j xi))
    (W : FiniteEtale U) [IsConnected W]
    (V : FiniteEtale X) (e : (FiniteEtale.pullback j).obj V ≅ W)
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (z : Spec (.of Ω') ⟶ ((show W.left ⟶ U from W.hom) ≫ j).normalization)
    (σ : Aut W)
    (hfix : z ≫ normalizationEndomorphism ((show W.left ⟶ U from W.hom) ≫ j)
      σ.hom.left (by rw [← Category.assoc]; exact congrArg (fun k => k ≫ j) σ.hom.w) = z) :
    σ = 1 := by
  let H := FiniteEtale.pullback j
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) H :=
    pullback_preservesLimitsOfShape_pempty j
  have hff : Nonempty H.FullyFaithful :=
    ((autHomOfCompIso_surjective_tfae (fiber (xi ≫ j)) (fiber xi) H
      (pullbackFiberIso j xi)).out 1 2).mp hsurj
  let ff : H.FullyFaithful := hff.some
  let eS : (H.obj V).left ≅ W.left :=
    ((FiniteEtale.forget U) ⋙ Over.forget U).mapIso e
  let : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  let : ConnectedSpace (H.obj V).left := eS.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  let : IsConnected (H.obj V) := isConnected_of_connectedSpace_left (H.obj V)
  let : IsConnected V := connected_of_connected_pullback j xi V
  let τ : Aut V := ff.preimageIso (e ≪≫ σ ≪≫ e.symm)
  have hτ : e.inv ≫ H.map τ.hom = σ.hom ≫ e.inv := by
    rw [show H.map τ.hom = (e ≪≫ σ ≪≫ e.symm).hom from ff.map_preimage _]
    change e.inv ≫ (e.hom ≫ σ.hom ≫ e.inv) = σ.hom ≫ e.inv
    exact e.inv_hom_id_assoc _
  let k : W.left ⟶ V.left := e.inv.left ≫ pullback.fst V.hom j
  have hk : k ≫ V.hom = (show W.left ⟶ U from W.hom) ≫ j := by
    have he : e.inv.left ≫ pullback.snd V.hom j = (show W.left ⟶ U from W.hom) := e.inv.w
    exact (Category.assoc e.inv.left (pullback.fst V.hom j) (show V.left ⟶ X from V.hom)).trans
      ((congrArg (fun t : (H.obj V).left ⟶ X => e.inv.left ≫ t)
        (pullback.condition (f := (show V.left ⟶ X from V.hom)) (g := j))).trans
        ((Category.assoc e.inv.left (pullback.snd V.hom j) j).symm.trans
          (congrArg (fun t : W.left ⟶ U => t ≫ j) he)))
  have hτk : σ.hom.left ≫ k = k ≫ τ.hom.left := by
    have he := congrArg (fun t : W ⟶ H.obj V => t.left) hτ
    change e.inv.left ≫ (H.map τ.hom).left = σ.hom.left ≫ e.inv.left at he
    have hp : (H.map τ.hom).left ≫ pullback.fst V.hom j =
        pullback.fst V.hom j ≫ τ.hom.left := pullback.lift_fst _ _ _
    exact (Category.assoc σ.hom.left e.inv.left (pullback.fst V.hom j)).symm.trans
      ((congrArg (fun t : W.left ⟶ (H.obj V).left => t ≫ pullback.fst V.hom j) he.symm).trans
        ((Category.assoc e.inv.left (H.map τ.hom).left (pullback.fst V.hom j)).trans
          ((congrArg (fun t : (H.obj V).left ⟶ V.left => e.inv.left ≫ t) hp).trans
            (Category.assoc e.inv.left (pullback.fst V.hom j) τ.hom.left).symm)))
  let f : W.left ⟶ X := (show W.left ⟶ U from W.hom) ≫ j
  let c : f.normalization ⟶ V.left := f.normalizationDesc k V.hom hk.symm
  have hc : c ≫ V.hom = f.fromNormalization := Scheme.Hom.normalizationDesc_comp _ _ _ _
  have hσf : σ.hom.left ≫ f = f := by
    dsimp only [f]
    rw [← Category.assoc]
    exact congrArg (fun t => t ≫ j) σ.hom.w
  have hcomm : normalizationEndomorphism f σ.hom.left hσf ≫ c = c ≫ τ.hom.left := by
    apply Scheme.Hom.normalization.hom_ext f _ _ V.hom
    · rw [← Category.assoc, toNormalization_normalizationEndomorphism,
        Category.assoc, Scheme.Hom.toNormalization_normalizationDesc,
        ← Category.assoc, Scheme.Hom.toNormalization_normalizationDesc, hτk]
    · rw [Category.assoc, hc, normalizationEndomorphism_fromNormalization]
    · have ht : τ.hom.left ≫ (show V.left ⟶ X from V.hom) = V.hom := τ.hom.w
      rw [Category.assoc, ht, hc]
  have hzc : (z ≫ c) ≫ τ.hom.left = z ≫ c := by
    rw [Category.assoc, ← hcomm, ← Category.assoc, hfix]
  let η : Spec (.of Ω') ⟶ X := (z ≫ c) ≫ V.hom
  let v : Over.mk η ⟶ V.toComma := Over.homMk (z ≫ c) rfl
  have hτone : τ = 1 := by
    apply evaluation_aut_injective_of_isConnected (fiber η) V
      ((fiberObjEquivHom η V).symm v)
    change (fiber η).map τ.hom ((fiberObjEquivHom η V).symm v) =
      (fiber η).map (𝟙 V) ((fiberObjEquivHom η V).symm v)
    rw [fiberObjEquivHom_symm_naturality, CategoryTheory.Functor.map_id]
    change (fiberObjEquivHom η V).symm (v ≫ τ.hom.hom) = (fiberObjEquivHom η V).symm v
    apply congrArg (fiberObjEquivHom η V).symm
    exact Over.OverMorphism.ext hzc
  have hσe : σ.hom ≫ e.inv = e.inv := by
    rw [← hτ, hτone]
    change e.inv ≫ H.map (𝟙 V) = e.inv
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  apply Aut.ext
  apply (cancel_mono e.inv).mp
  exact hσe.trans (Category.id_comp e.inv).symm

end EtaleFundamentalGroups.Inertia
