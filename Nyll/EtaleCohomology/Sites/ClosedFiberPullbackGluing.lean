/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleCohomology.Sites.ClosedFiberFinitePullbackLifts
import Nyll.EtaleCohomology.Sites.PullbackClosedFiberStalks
import Nyll.EtaleCohomology.Sites.PullbackSections
import Nyll.EtaleCohomology.Sites.ModuleSetComparison
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
import Nyll.EtaleCohomology.Sites.ZariskiModuleBaseChange
import Nyll.EtaleCohomology.Sites.ZariskiRestriction
import Nyll.SchemeTheory.Morphisms.ProperHenselianSheafRestriction
import Nyll.SchemeTheory.Topology.SheafPullbackStalks
import Nyll.SchemeTheory.Topology.SpecializationCofinalRestriction
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Stalks

/-!
# Gluing the actual closed-fiber unit after finite refinement

The concrete local preimages on a finite refinement glue on its closed
fiber: the original unit, pulled back to that refinement, is injective on
the relevant Zariski stalks. Proper henselian restriction then lifts this
closed-fiber section to the whole refinement. The section equations use
the original unit throughout.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace EtaleCohomology

private theorem exists_global_lift_of_mono_of_local_lifts
    {T : TopCat.{u}}
    {F G : TopCat.Sheaf (Type u) T}
    (m : F ⟶ G) [Mono m] (t : G.obj.obj (op (⊤ : Opens T)))
    (hlift : ∀ x : T, ∃ U : Opens T, x ∈ U ∧
      ∃ a : F.obj.obj (op U), m.hom.app (op U) a =
        G.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op t) :
    ∃ a : F.obj.obj (op (⊤ : Opens T)), m.hom.app (op ⊤) a = t := by
  classical
  choose U hx a ha using hlift
  let FP : T.Presheaf (Type u) := F.obj
  let GP : T.Presheaf (Type u) := G.obj
  let j : ∀ x : T, U x ⟶ (⊤ : Opens T) := fun _ => homOfLE le_top
  have hcover : (⊤ : Opens T) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hmP : Mono m.hom := (TopCat.Sheaf.forget (Type u) T).map_mono m
  have hmU (W : Opens T) : Mono (m.hom.app (op W)) :=
    (NatTrans.mono_iff_mono_app m.hom).mp hmP (op W)
  have hcompat : TopCat.Presheaf.IsCompatible FP U a := by
    intro x y
    apply (CategoryTheory.mono_iff_injective (m.hom.app (op (U x ⊓ U y)))).mp
      (hmU (U x ⊓ U y))
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      m.hom.naturality, m.hom.naturality, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, ha x, ha y]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← GP.map_comp, ← GP.map_comp]
    rfl
  obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' F U ⊤ j hcover a hcompat
  refine ⟨s, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' G U ⊤ j hcover
  intro x
  rw [← ConcreteCategory.comp_apply, ← m.hom.naturality,
    ConcreteCategory.comp_apply, hs x]
  exact ha x

private theorem exists_pullback_lift_of_image_stalk_mono
    {S T : TopCat.{u}} (i : S ⟶ T)
    {F G : TopCat.Sheaf (Type u) T}
    (m : F ⟶ G)
    (hm : ∀ x : S, Mono ((TopCat.Presheaf.stalkFunctor (Type u) (i x)).map m.hom))
    (t : G.obj.obj (op (⊤ : Opens T)))
    (hlift : ∀ x : S, ∃ U : Opens T, i x ∈ U ∧
      ∃ a : F.obj.obj (op U), m.hom.app (op U) a =
        G.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op t) :
    ∃ a : ((TopCat.Sheaf.pullback (Type u) i).obj F).obj.obj
        (op ((Opens.map i).obj ⊤)),
      ((TopCat.Sheaf.pullback (Type u) i).map m).hom.app
          (op ((Opens.map i).obj ⊤)) a =
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app G).hom.app
          (op (⊤ : Opens T))) t := by
  let L : TopCat.Sheaf (Type u) T ⥤ TopCat.Sheaf (Type u) S :=
    TopCat.Sheaf.pullback (Type u) i
  let FQ : S.Presheaf (Type u) := (L.obj F).obj
  let GQ : S.Presheaf (Type u) := (L.obj G).obj
  let mQ : L.obj F ⟶ L.obj G := L.map m
  have hmQ : Mono mQ := by
    apply (TopCat.Presheaf.mono_iff_stalk_mono mQ).mpr
    intro x
    let FP : T.Presheaf (Type u) := F.obj
    let GP : T.Presheaf (Type u) := G.obj
    let eF : FP.stalk (i x) ≅ FQ.stalk x := SchemeTheory.sheafStalkPullbackIso i F x
    let eG : GP.stalk (i x) ≅ GQ.stalk x := SchemeTheory.sheafStalkPullbackIso i G x
    let mT : FP.stalk (i x) ⟶ GP.stalk (i x) :=
      (TopCat.Presheaf.stalkFunctor (Type u) (i x)).map m.hom
    let mS : FQ.stalk x ⟶ GQ.stalk x :=
      (TopCat.Presheaf.stalkFunctor (Type u) x).map mQ.hom
    have hn : mT ≫ eG.hom = eF.hom ≫ mS :=
      SchemeTheory.sheafStalkPullbackIso_hom_naturality i m x
    have heq : mS = eF.inv ≫ mT ≫ eG.hom := by
      rw [hn, eF.inv_hom_id_assoc]
    have hcomp : Mono (eF.inv ≫ mT ≫ eG.hom) :=
      mono_comp' (inferInstanceAs (Mono eF.inv))
        (mono_comp' (hm x) (inferInstanceAs (Mono eG.hom)))
    change Mono mS
    exact heq.symm ▸ hcomp
  let FP : T.Presheaf (Type u) := F.obj
  let GP : T.Presheaf (Type u) := G.obj
  let ηF : FP ⟶ (TopCat.Presheaf.pushforward (Type u) i).obj FQ :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F).hom
  let ηG : GP ⟶ (TopCat.Presheaf.pushforward (Type u) i).obj GQ :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app G).hom
  let tQ : GQ.obj (op (⊤ : Opens S)) := ηG.app (op ⊤) t
  apply exists_global_lift_of_mono_of_local_lifts mQ tQ
  intro x
  obtain ⟨U, hxU, a, ha⟩ := hlift x
  let V : Opens S := (Opens.map i).obj U
  let b : FQ.obj (op V) := ηF.app (op U) a
  refine ⟨V, hxU, b, ?_⟩
  have hn : m.hom ≫ ηG =
      ηF ≫ (TopCat.Presheaf.pushforward (Type u) i).map mQ.hom :=
    congrArg (fun k : F ⟶ (TopCat.Sheaf.pushforward (Type u) i).obj (L.obj G) => k.hom)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.naturality m)
  have hnU : ηG.app (op U) (m.hom.app (op U) a) =
      mQ.hom.app (op V) b :=
    congrArg (fun k : FP ⟶ (TopCat.Presheaf.pushforward (Type u) i).obj GQ =>
      k.app (op U) a) hn
  rw [← hnU, ha]
  exact congrArg (fun k : GP.obj (op (⊤ : Opens T)) ⟶ GQ.obj (op V) => k t)
    (ηG.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)

/-- An actual closed-fiber section lifts globally after a finite surjective
refinement of the original proper scheme. -/
theorem exists_finite_refinement_global_pullback_lift
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i : pullback f r ⟶ X := pullback.fst f r
    let G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
      (etalePushforward i Λ).obj ((etalePullback i Λ).obj F)
    let η : F ⟶ G := (etalePullbackPushforwardAdjunction i Λ).unit.app F
    ∀ t : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
      ∃ (Y : Scheme.{u}) (q : Y ⟶ X), IsFinite q ∧ Surjective q ∧
        ∃ b : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))),
          ((etalePullback q Λ).map η).hom.app (op (Scheme.Etale.mk (𝟙 Y))) b =
            etalePullbackGlobalSectionsMap q Λ G t := by
  intro r i G η t
  have : IsClosedImmersion r := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (IsLocalRing.residue R)) IsLocalRing.residue_surjective
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.fst f r))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨Y, q, hfinite, hsurj, hlift⟩ :=
    exists_finite_refinement_zariski_pullback_lifts i Λ F t
  refine ⟨Y, q, hfinite, hsurj, ?_⟩
  have : IsFinite q := hfinite
  let T : TopCat.{u} := TopCat.of Y
  let C : Set T := (q ≫ f) ⁻¹' {IsLocalRing.closedPoint R}
  let S : TopCat.{u} := TopCat.of C
  let j : S ⟶ T := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let Fq := (etalePullback q Λ).obj F
  let Gq := (etalePullback q Λ).obj G
  let μ : Fq ⟶ Gq := (etalePullback q Λ).map η
  let H : CategoryTheory.Sheaf (Opens.grothendieckTopology T) (Type u) :=
    (etaleModuleZariskiRestriction Y Λ).obj Fq
  let K : CategoryTheory.Sheaf (Opens.grothendieckTopology T) (Type u) :=
    (etaleModuleZariskiRestriction Y Λ).obj Gq
  let m : H ⟶ K := (etaleModuleZariskiRestriction Y Λ).map μ
  let eH := etaleZariskiGlobalSectionsIso Y (Type u) ((etaleModuleUnderlying Y Λ).obj Fq)
  let eK := etaleZariskiGlobalSectionsIso Y (Type u) ((etaleModuleUnderlying Y Λ).obj Gq)
  let tq := etalePullbackGlobalSectionsMap q Λ G t
  let tK : K.obj.obj (op (⊤ : Opens T)) := eK.inv tq
  have hm (y : S) : Mono ((TopCat.Presheaf.stalkFunctor (Type u) (j y)).map m.hom) := by
    have hy : f (q y.val) = IsLocalRing.closedPoint R :=
      (Scheme.Hom.comp_apply q f y.val).symm.trans y.property
    exact etalePullbackClosedFiberUnit_zariskiStalk_mono R f q Λ F y.val hy
  have hlocal (y : S) : ∃ U : Opens T, j y ∈ U ∧
      ∃ a : H.obj.obj (op U), m.hom.app (op U) a =
        K.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op tK := by
    obtain ⟨U, hyU, a, ha⟩ := hlift y.val
    refine ⟨U, hyU, a, ?_⟩
    have he := etaleZariskiGlobalSectionsIso_inv_restrict Y (Type u)
      ((etaleModuleUnderlying Y Λ).obj Gq) U
    exact ha.trans
      (congrArg (fun k : ((etaleModuleUnderlying Y Λ).obj Gq).obj.obj
        (op (Scheme.Etale.mk (𝟙 Y))) ⟶ K.obj.obj (op U) => k tq) he).symm
  obtain ⟨aC, haC⟩ := exists_pullback_lift_of_image_stalk_mono j m hm tK hlocal
  obtain ⟨aH, haH⟩ := (AlgebraicGeometry.sheaf_closedFiber_restriction_bijective
    (q ≫ f) H).surjective aC
  have ha : m.hom.app (op ⊤) aH = tK := by
    apply (AlgebraicGeometry.sheaf_closedFiber_restriction_bijective (q ≫ f) K).injective
    have hn := congrArg
      (fun k : H ⟶ (TopCat.Sheaf.pushforward (Type u) j).obj
        ((TopCat.Sheaf.pullback (Type u) j).obj K) => k.hom.app (op ⊤) aH)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) j).unit.naturality m)
    exact hn.trans ((congrArg
      (((TopCat.Sheaf.pullback (Type u) j).map m).hom.app
        (op ((Opens.map j).obj ⊤))) haH).trans haC)
  refine ⟨eH.hom aH, ?_⟩
  apply eK.toEquiv.symm.injective
  let μ₀ := (etaleModuleUnderlying Y Λ).map μ
  have hn := congrArg
    (fun k : ((etaleModuleUnderlying Y Λ).obj Fq).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y))) ⟶ K.obj.obj (op (⊤ : Opens T)) => k (eH.hom aH))
    (μ₀.hom.naturality (zariskiToEtaleTopIso Y).hom.op)
  have heH : eH.inv (eH.hom aH) = aH := eH.toEquiv.symm_apply_apply aH
  exact hn.symm.trans ((congrArg (m.hom.app (op ⊤)) heH).trans ha)

end EtaleCohomology
