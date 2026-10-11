/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import EtaleCohomology.Sites.PullbackClosedFiberStalks
import EtaleCohomology.Sites.ModuleSetComparison
import EtaleCohomology.Sites.SheafFunctors
import EtaleCohomology.Sites.ZariskiGlobalSections
import EtaleCohomology.Sites.ZariskiModuleBaseChange
import SchemeTheory.Morphisms.ProperHenselianClosedRestriction
import SchemeTheory.Topology.SpecializationCofinalSections
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Sheaves.Stalks

/-!
# Global injectivity of the pulled-back original closed-fiber unit

The original unit remains injective on global sections after any pullback
whose source is proper over the henselian local base. Its actual Zariski
stalk maps are injective along that source's closed fiber, and those germs
detect global sections. This uses the same original unit, without a new
comparison with a different closed-fiber adjunction.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace EtaleCohomology

/-- The original closed-fiber unit is globally injective after pullback
to any scheme proper over the original henselian local base. -/
theorem etalePullbackClosedFiberUnit_globalSections_injective
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ X)
    [IsProper (q ≫ f)]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i : pullback f r ⟶ X := pullback.fst f r
    let η : F ⟶ (etalePushforward i Λ).obj ((etalePullback i Λ).obj F) :=
      (etalePullbackPushforwardAdjunction i Λ).unit.app F
    Function.Injective
      (((etalePullback q Λ).map η).hom.app (op (Scheme.Etale.mk (𝟙 Y)))) := by
  intro r i η a b hab
  let T : TopCat.{u} := TopCat.of Y
  let Fq := (etalePullback q Λ).obj F
  let Gq := (etalePullback q Λ).obj
    ((etalePushforward i Λ).obj ((etalePullback i Λ).obj F))
  let μ : Fq ⟶ Gq := (etalePullback q Λ).map η
  let H : CategoryTheory.Sheaf (Opens.grothendieckTopology T) (Type u) :=
    (etaleModuleZariskiRestriction Y Λ).obj Fq
  let K : CategoryTheory.Sheaf (Opens.grothendieckTopology T) (Type u) :=
    (etaleModuleZariskiRestriction Y Λ).obj Gq
  let m : H ⟶ K := (etaleModuleZariskiRestriction Y Λ).map μ
  let eH := etaleZariskiGlobalSectionsIso Y (Type u) ((etaleModuleUnderlying Y Λ).obj Fq)
  let eK := etaleZariskiGlobalSectionsIso Y (Type u) ((etaleModuleUnderlying Y Λ).obj Gq)
  let μ₀ := (etaleModuleUnderlying Y Λ).map μ
  have hn : eH.inv ≫ m.hom.app (op ⊤) =
      μ₀.hom.app (op (Scheme.Etale.mk (𝟙 Y))) ≫ eK.inv :=
    μ₀.hom.naturality (zariskiToEtaleTopIso Y).hom.op
  have htop : m.hom.app (op ⊤) (eH.inv a) = m.hom.app (op ⊤) (eH.inv b) := by
    have ha := congrArg (fun k : ((etaleModuleUnderlying Y Λ).obj Fq).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y))) ⟶ K.obj.obj (op (⊤ : Opens T)) => k a) hn
    have hb := congrArg (fun k : ((etaleModuleUnderlying Y Λ).obj Fq).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y))) ⟶ K.obj.obj (op (⊤ : Opens T)) => k b) hn
    exact ha.trans ((congrArg eK.inv hab).trans hb.symm)
  apply eH.toEquiv.symm.injective
  let C : Set T := (q ≫ f) ⁻¹' {IsLocalRing.closedPoint R}
  have hcofinal : ∀ y : T, ∃ z ∈ C, y ⤳ z := by
    intro y
    obtain ⟨z, hzC, hyz⟩ := (isConnected_closedFiber_inter_closure (q ≫ f) y).nonempty
    exact ⟨z, hzC, specializes_iff_mem_closure.mpr hyz⟩
  apply SchemeTheory.globalSection_eq_of_germs_on_specialization_cofinal
    hcofinal H (eH.inv a) (eH.inv b)
  intro z hz
  have hz' : f (q z) = IsLocalRing.closedPoint R :=
    (Scheme.Hom.comp_apply q f z).symm.trans hz
  have hm : Mono ((TopCat.Presheaf.stalkFunctor (Type u) z).map m.hom) :=
    etalePullbackClosedFiberUnit_zariskiStalk_mono R f q Λ F z hz'
  apply (CategoryTheory.mono_iff_injective
    ((TopCat.Presheaf.stalkFunctor (Type u) z).map m.hom)).mp hm
  let HP : T.Presheaf (Type u) := H.obj
  let KP : T.Presheaf (Type u) := K.obj
  let hzTop : z ∈ (⊤ : Opens T) := trivial
  have ha := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (F := HP) (G := KP) (⊤ : Opens T) z hzTop m.hom (eH.inv a)
  have hb := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (F := HP) (G := KP) (⊤ : Opens T) z hzTop m.hom (eH.inv b)
  exact ha.trans ((congrArg (KP.germ ⊤ z hzTop) htop).trans hb.symm)

end EtaleCohomology
