/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.SchemePairDescent
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Stage Recovery

A constant-field stage with its coefficient structure.
-/

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
namespace EtaleFundamentalGroups
variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- A constant-field stage with its coefficient structure. -/
abbrev constantFieldStageOver (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (s : Finset L) :
    Over (Spec (CommRingCat.of (IntermediateField.adjoin k (s : Set L)))) :=
  Over.mk (pullback.fst (Spec.map (CommRingCat.ofHom
    (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f)

/-- The actual coefficient cone square identifies a full extension with the
coefficient pullback of its finite stage. -/
def constantFieldStagePullbackIso
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) (s : Finset L) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ≅
      pullback
        (pullback.fst (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f)
        (Spec.map (CommRingCat.ofHom
          (IntermediateField.adjoin k (s : Set L)).val.toRingHom)) :=
  (constantFieldInverseLimitCone_π_app_isPullback k L X f s).isoPullback

@[reassoc]
theorem constantFieldStagePullbackIso_hom_fst
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) (s : Finset L) :
    (constantFieldStagePullbackIso k L X f s).hom ≫ pullback.fst _ _ =
      (constantFieldInverseLimitCone k L X f).π.app (op s) :=
  (constantFieldInverseLimitCone_π_app_isPullback k L X f s).isoPullback_hom_fst

@[reassoc]
theorem constantFieldStagePullbackIso_hom_snd
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) (s : Finset L) :
    (constantFieldStagePullbackIso k L X f s).hom ≫ pullback.snd _ _ =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k L))) f :=
  (constantFieldInverseLimitCone_π_app_isPullback k L X f s).isoPullback_hom_snd

/-- The recovery equation returned by actual scheme-pair descent is precisely
naturality for the coefficient pullback of the finite-stage map. -/
theorem constantFieldStagePullbackIso_naturality
    (X Y : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (s : Finset L)
    (a : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) g)
    (b : pullback (Spec.map (CommRingCat.ofHom
        (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f ⟶
      pullback (Spec.map (CommRingCat.ofHom
        (algebraMap k (IntermediateField.adjoin k (s : Set L))))) g)
    (ha : a ≫ pullback.fst _ g = pullback.fst _ f)
    (hb : b ≫ pullback.fst _ g = pullback.fst _ f)
    (hab : (constantFieldInverseLimitCone k L X f).π.app (op s) ≫ b =
      a ≫ (constantFieldInverseLimitCone k L Y g).π.app (op s)) :
    (constantFieldStagePullbackIso k L X f s).hom ≫
      ((Over.pullback (Spec.map (CommRingCat.ofHom
        (IntermediateField.adjoin k (s : Set L)).val.toRingHom))).map
          (Over.homMk (U := constantFieldStageOver k L X f s)
            (V := constantFieldStageOver k L Y g s) b hb)).left =
      a ≫ (constantFieldStagePullbackIso k L Y g s).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst,
      constantFieldStageOver, Over.mk_hom, Over.homMk_left]
    rw [constantFieldStagePullbackIso_hom_fst_assoc,
      constantFieldStagePullbackIso_hom_fst]
    exact hab
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd,
      constantFieldStageOver, Over.mk_hom]
    rw [constantFieldStagePullbackIso_hom_snd, constantFieldStagePullbackIso_hom_snd, ha]

/-- Recovered chart maps compose with the pulled-back finite-stage map exactly
as their actual full-extension counterparts. -/
theorem constantFieldStagePullbackIso_recovered_comp
    (X Y Z : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (s : Finset L)
    (a : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) g)
    (b : pullback (Spec.map (CommRingCat.ofHom
        (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f ⟶
      pullback (Spec.map (CommRingCat.ofHom
        (algebraMap k (IntermediateField.adjoin k (s : Set L))))) g)
    (ha : a ≫ pullback.fst _ g = pullback.fst _ f)
    (hb : b ≫ pullback.fst _ g = pullback.fst _ f)
    (hab : (constantFieldInverseLimitCone k L X f).π.app (op s) ≫ b =
      a ≫ (constantFieldInverseLimitCone k L Y g).π.app (op s))
    (h : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) g ⟶ Z) :
    ((Over.pullback (Spec.map (CommRingCat.ofHom
      (IntermediateField.adjoin k (s : Set L)).val.toRingHom))).map
        (Over.homMk (U := constantFieldStageOver k L X f s)
          (V := constantFieldStageOver k L Y g s) b hb)).left ≫
      (constantFieldStagePullbackIso k L Y g s).inv ≫ h =
      (constantFieldStagePullbackIso k L X f s).inv ≫ a ≫ h := by
  apply (cancel_epi (constantFieldStagePullbackIso k L X f s).hom).mp
  rw [← Category.assoc,
    constantFieldStagePullbackIso_naturality k L X Y f g s a b ha hb hab]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Recovery of a transition and its two chart inclusions gives the recovered
chart compatibility needed for actual finite-stage gluing. -/
theorem constantFieldStage_recovered_transition
    (A C V W Z : Scheme.{u})
    (fA : A ⟶ Spec (CommRingCat.of k)) (fC : C ⟶ Spec (CommRingCat.of k))
    (fV : V ⟶ Spec (CommRingCat.of k)) (fW : W ⟶ Spec (CommRingCat.of k))
    (s : Finset L)
    (tL : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) fV ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) fW)
    (dL : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) fW ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) fC)
    (cL : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) fV ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) fA)
    (tE : constantFieldStageOver k L V fV s ⟶ constantFieldStageOver k L W fW s)
    (dE : constantFieldStageOver k L W fW s ⟶ constantFieldStageOver k L C fC s)
    (cE : constantFieldStageOver k L V fV s ⟶ constantFieldStageOver k L A fA s)
    (htL : tL ≫ pullback.fst _ fW = pullback.fst _ fV)
    (hdL : dL ≫ pullback.fst _ fC = pullback.fst _ fW)
    (hcL : cL ≫ pullback.fst _ fA = pullback.fst _ fV)
    (htE : (constantFieldInverseLimitCone k L V fV).π.app (op s) ≫ tE.left =
      tL ≫ (constantFieldInverseLimitCone k L W fW).π.app (op s))
    (hdE : (constantFieldInverseLimitCone k L W fW).π.app (op s) ≫ dE.left =
      dL ≫ (constantFieldInverseLimitCone k L C fC).π.app (op s))
    (hcE : (constantFieldInverseLimitCone k L V fV).π.app (op s) ≫ cE.left =
      cL ≫ (constantFieldInverseLimitCone k L A fA).π.app (op s))
    (hA : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) fA ⟶ Z)
    (hC : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) fC ⟶ Z)
    (hcompat : tL ≫ dL ≫ hC = cL ≫ hA) :
    ((Over.pullback (Spec.map (CommRingCat.ofHom
      (IntermediateField.adjoin k (s : Set L)).val.toRingHom))).map tE).left ≫
      ((Over.pullback (Spec.map (CommRingCat.ofHom
        (IntermediateField.adjoin k (s : Set L)).val.toRingHom))).map dE).left ≫
        (constantFieldStagePullbackIso k L C fC s).inv ≫ hC =
    ((Over.pullback (Spec.map (CommRingCat.ofHom
      (IntermediateField.adjoin k (s : Set L)).val.toRingHom))).map cE).left ≫
        (constantFieldStagePullbackIso k L A fA s).inv ≫ hA := by
  have hd := constantFieldStagePullbackIso_recovered_comp k L W C Z fW fC s
    dL dE.left hdL dE.w hdE hC
  have hc := constantFieldStagePullbackIso_recovered_comp k L V A Z fV fA s
    cL cE.left hcL cE.w hcE hA
  have ht := constantFieldStagePullbackIso_recovered_comp k L V W Z fV fW s
    tL tE.left htL tE.w htE (dL ≫ hC)
  simp only [Over.homMk_eta] at hd hc ht
  rw [hd, ht, hcompat, hc]

end EtaleFundamentalGroups
