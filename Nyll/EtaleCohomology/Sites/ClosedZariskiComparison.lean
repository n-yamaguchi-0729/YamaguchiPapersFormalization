/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleCohomology.Sites.ZariskiGeometricStalks
import Nyll.EtaleCohomology.Sites.ZariskiModuleBaseChange
import Nyll.EtaleCohomology.Sites.ClosedAdjunction
import Nyll.SchemeTheory.Topology.SheafPullbackStalks
import Nyll.SchemeTheory.Topology.SheafPullbackGerms
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Topology.Sheaves.Stalks

/-!
# The closed-immersion Zariski comparison is a monomorphism

The module-valued closed adjunction unit is an isomorphism on geometric
stalks inside the closed subscheme. The injective map from Zariski germs to
geometric germs makes its underlying Zariski stalk map injective there.
The actual mixed unit square and the topological inverse-image stalk
formula then prove that the constructed comparison is a monomorphism.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace EtaleCohomology

private lemma zariskiStalkComparison_naturality
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) (ξ : Spec (CommRingCat.of Ω))
    {F G : Sheaf X.smallEtaleTopology (Type u)} (η : F ⟶ G) :
    (TopCat.Presheaf.stalkFunctor (Type u) (s ξ)).map
        ((etaleZariskiRestriction X (Type u)).map η).hom ≫
        etaleZariskiStalkToGeometricStalk s ξ G =
      etaleZariskiStalkToGeometricStalk s ξ F ≫
        (Scheme.pointSmallEtale s).presheafFiber.map η.hom := by
  let TX : TopCat.{u} := X.toPresheafedSpace
  let P : TX.Presheaf (Type u) := ((etaleZariskiRestriction X (Type u)).obj F).obj
  let Q : TX.Presheaf (Type u) := ((etaleZariskiRestriction X (Type u)).obj G).obj
  let m : P ⟶ Q := ((etaleZariskiRestriction X (Type u)).map η).hom
  let S : TX.Presheaf (Type u) ⥤ Type u := TopCat.Presheaf.stalkFunctor (Type u) (s ξ)
  let Φ := Scheme.pointSmallEtale s
  let TΦ : (X.Etaleᵒᵖ ⥤ Type u) ⥤ Type u := Φ.presheafFiber
  let kF : P.stalk (s ξ) ⟶ TΦ.obj F.obj := etaleZariskiStalkToGeometricStalk s ξ F
  let kG : Q.stalk (s ξ) ⟶ TΦ.obj G.obj := etaleZariskiStalkToGeometricStalk s ξ G
  let mΦ : TΦ.obj F.obj ⟶ TΦ.obj G.obj := TΦ.map η.hom
  change S.map m ≫ kG = kF ≫ mΦ
  refine TopCat.Presheaf.stalk_hom_ext P (fun U hU => ?_)
  let A : Type u := F.obj.obj (op ((zariskiToEtale X).obj U))
  let B : Type u := G.obj.obj (op ((zariskiToEtale X).obj U))
  let mU : A ⟶ B := η.hom.app (op ((zariskiToEtale X).obj U))
  let gP : A ⟶ P.stalk (s ξ) := P.germ U (s ξ) hU
  let gQ : B ⟶ Q.stalk (s ξ) := Q.germ U (s ξ) hU
  let gF : A ⟶ TΦ.obj F.obj := Φ.toPresheafFiber ((zariskiToEtale X).obj U)
    (zariskiGeometricLift s ξ U hU) F.obj
  let gG : B ⟶ TΦ.obj G.obj := Φ.toPresheafFiber ((zariskiToEtale X).obj U)
    (zariskiGeometricLift s ξ U hU) G.obj
  have hm : gP ≫ S.map m = mU ≫ gQ :=
    TopCat.Presheaf.stalkFunctor_map_germ U (s ξ) hU m
  have hkF : gP ≫ kF = gF := germ_etaleZariskiStalkToGeometricStalk s ξ F U hU
  have hkG : gQ ≫ kG = gG := germ_etaleZariskiStalkToGeometricStalk s ξ G U hU
  have hΦ : gF ≫ mΦ = mU ≫ gG :=
    Φ.toPresheafFiber_naturality η.hom ((zariskiToEtale X).obj U)
      (zariskiGeometricLift s ξ U hU)
  change gP ≫ (S.map m ≫ kG) = gP ≫ (kF ≫ mΦ)
  calc
    gP ≫ (S.map m ≫ kG) = (gP ≫ S.map m) ≫ kG := (Category.assoc _ _ _).symm
    _ = (mU ≫ gQ) ≫ kG := congrArg (fun a => a ≫ kG) hm
    _ = mU ≫ gG := by rw [Category.assoc, hkG]
    _ = gF ≫ mΦ := hΦ.symm
    _ = (gP ≫ kF) ≫ mΦ := congrArg (fun a => a ≫ mΦ) hkF.symm
    _ = gP ≫ (kF ≫ mΦ) := Category.assoc _ _ _

/-- Injectivity at a geometric stalk detects injectivity on the actual Zariski stalk. -/
lemma etaleZariski_stalk_map_mono_of_geometric
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) (ξ : Spec (CommRingCat.of Ω))
    {F G : Sheaf X.smallEtaleTopology (Type u)} (η : F ⟶ G)
    [Mono ((Scheme.pointSmallEtale s).presheafFiber.map η.hom)] :
    Mono ((TopCat.Presheaf.stalkFunctor (Type u) (s ξ)).map
      ((etaleZariskiRestriction X (Type u)).map η).hom) := by
  let TX : TopCat.{u} := X.toPresheafedSpace
  let P : TX.Presheaf (Type u) := ((etaleZariskiRestriction X (Type u)).obj F).obj
  let Q : TX.Presheaf (Type u) := ((etaleZariskiRestriction X (Type u)).obj G).obj
  let TΦ : (X.Etaleᵒᵖ ⥤ Type u) ⥤ Type u := (Scheme.pointSmallEtale s).presheafFiber
  let m : P.stalk (s ξ) ⟶ Q.stalk (s ξ) :=
    (TopCat.Presheaf.stalkFunctor (Type u) (s ξ)).map
      ((etaleZariskiRestriction X (Type u)).map η).hom
  let kF : P.stalk (s ξ) ⟶ TΦ.obj F.obj := etaleZariskiStalkToGeometricStalk s ξ F
  let kG : Q.stalk (s ξ) ⟶ TΦ.obj G.obj := etaleZariskiStalkToGeometricStalk s ξ G
  let mΦ : TΦ.obj F.obj ⟶ TΦ.obj G.obj := TΦ.map η.hom
  have hkF : Mono kF :=
    (mono_iff_injective kF).mpr (etaleZariskiStalkToGeometricStalk_injective s ξ F)
  have hgeo : Mono mΦ := inferInstance
  have hcomp : Mono (kF ≫ mΦ) := mono_comp' hkF hgeo
  have heq : m ≫ kG = kF ≫ mΦ := zariskiStalkComparison_naturality s ξ η
  have : Mono (m ≫ kG) := heq.symm ▸ hcomp
  exact mono_of_mono m kG

/-- The actual closed adjunction unit is injective on Zariski stalks along
the closed subscheme, after forgetting the module structure. -/
lemma etaleClosedUnit_zariskiStalk_mono
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (z : Z) :
    Mono ((TopCat.Presheaf.stalkFunctor (Type u) (i z)).map
      ((etaleModuleZariskiRestriction X Λ).map
        ((etalePullbackPushforwardAdjunction i Λ).unit.app F)).hom) := by
  have : X.smallEtaleTopology.HasSheafCompose (forget (ModuleCat.{u} Λ)) := by
    let : PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ)) :=
      (ModuleCat.adj Λ).rightAdjoint_preservesLimits
    exact hasSheafCompose_of_preservesLimitsOfSize
      (F := forget (ModuleCat.{u} Λ)) X.smallEtaleTopology
  let Ω : Type u := SeparableClosure (Z.residueField z)
  let s : Spec (CommRingCat.of Ω) ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) Ω)) ≫
      Z.fromSpecResidueField z
  let ξ : Spec (CommRingCat.of Ω) := default
  have hs : s ξ = z := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply z _
  let Φ := Scheme.pointSmallEtale (s ≫ i)
  let η := (etalePullbackPushforwardAdjunction i Λ).unit.app F
  let η₀ := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u} Λ))).map η
  have : IsIso (Φ.sheafFiber.map η) := etalePushforwardClosed_unit_stalk_isIso i Λ s F
  have hη₀ : IsIso (Φ.sheafFiber.map η₀) :=
    (NatIso.isIso_map_iff (Φ.sheafFiberCompIso (forget (ModuleCat.{u} Λ))) η).mpr
      (inferInstanceAs (IsIso ((forget (ModuleCat.{u} Λ)).map (Φ.sheafFiber.map η))))
  have : Mono (Φ.presheafFiber.map η₀.hom) := inferInstanceAs (Mono (Φ.sheafFiber.map η₀))
  have hpoint : (s ≫ i) ξ = i z := (Scheme.Hom.comp_apply s i ξ).trans (congrArg i hs)
  rw [← hpoint]
  exact etaleZariski_stalk_map_mono_of_geometric (s ≫ i) ξ η₀

/-- For a closed immersion, topological inverse image of the underlying
Zariski sheaf embeds into the underlying actual étale inverse image. -/
theorem etaleModuleZariskiPullbackComparison_mono
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Mono ((etaleModuleZariskiPullbackComparison i Λ).app F) := by
  let TX : TopCat.{u} := X.toPresheafedSpace
  let TZ : TopCat.{u} := Z.toPresheafedSpace
  let JX : GrothendieckTopology (Opens TX) := Opens.grothendieckTopology TX
  let JZ : GrothendieckTopology (Opens TZ) := Opens.grothendieckTopology TZ
  let f : TZ ⟶ TX := i.base
  let H : Sheaf JX (Type u) := (etaleModuleZariskiRestriction X Λ).obj F
  let L : Sheaf JZ (Type u) := (TopCat.Sheaf.pullback (Type u) f).obj H
  let G : Sheaf JZ (Type u) :=
    (etaleModuleZariskiRestriction Z Λ).obj ((etalePullback i Λ).obj F)
  let c : L ⟶ G := (etaleModuleZariskiPullbackComparison i Λ).app F
  let E : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
    (etalePushforward i Λ).obj ((etalePullback i Λ).obj F)
  let η : F ⟶ E := (etalePullbackPushforwardAdjunction i Λ).unit.app F
  let B : Sheaf JX (Type u) := (etaleModuleZariskiRestriction X Λ).obj E
  let e : B ≅ (TopCat.Sheaf.pushforward (Type u) f).obj G :=
    (etaleModuleZariskiPushforwardIso i Λ).app ((etalePullback i Λ).obj F)
  let α : H ⟶ (TopCat.Sheaf.pushforward (Type u) f).obj G :=
    (etaleModuleZariskiRestriction X Λ).map η ≫ e.hom
  let ηT : H ⟶ (TopCat.Sheaf.pushforward (Type u) f).obj L :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H
  have hα : α = ηT ≫ (TopCat.Sheaf.pushforward (Type u) f).map c :=
    etaleModuleZariskiPullbackComparison_unit i Λ F
  apply (TopCat.Presheaf.mono_iff_stalk_mono c).mpr
  intro z
  let P : TX.Presheaf (Type u) := H.obj
  let Q : TZ.Presheaf (Type u) := L.obj
  let T : TZ.Presheaf (Type u) := G.obj
  let αP : P ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj T := α.hom
  let cP : Q ⟶ T := c.hom
  let ηP : P ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj Q := ηT.hom
  let Sₓ : TX.Presheaf (Type u) ⥤ Type u := TopCat.Presheaf.stalkFunctor (Type u) (f z)
  let S𝓏 : TZ.Presheaf (Type u) ⥤ Type u := TopCat.Presheaf.stalkFunctor (Type u) z
  let eₛ : P.stalk (f z) ≅ Q.stalk z := SchemeTheory.sheafStalkPullbackIso f H z
  let m : Q.stalk z ⟶ T.stalk z := S𝓏.map cP
  let p : ((TopCat.Presheaf.pushforward (Type u) f).obj T).stalk (f z) ⟶ T.stalk z :=
    T.stalkPushforward (Type u) f z
  have heq : Sₓ.map αP ≫ p = eₛ.hom ≫ m := by
    refine TopCat.Presheaf.stalk_hom_ext P (fun U hU => ?_)
    let V : Opens TZ := (Opens.map f).obj U
    have hzV : z ∈ V := hU
    let aU : P.obj (op U) ⟶ T.obj (op V) := αP.app (op U)
    let uU : P.obj (op U) ⟶ Q.obj (op V) := ηP.app (op U)
    let cV : Q.obj (op V) ⟶ T.obj (op V) := cP.app (op V)
    let gP : P.obj (op U) ⟶ P.stalk (f z) := P.germ U (f z) hU
    let gQ : Q.obj (op V) ⟶ Q.stalk z := Q.germ V z hzV
    let gT : T.obj (op V) ⟶ T.stalk z := T.germ V z hzV
    let gPush : T.obj (op V) ⟶
        ((TopCat.Presheaf.pushforward (Type u) f).obj T).stalk (f z) :=
      ((TopCat.Presheaf.pushforward (Type u) f).obj T).germ U (f z) hU
    have haU : aU = uU ≫ cV :=
      congrArg (fun a : H ⟶ (TopCat.Sheaf.pushforward (Type u) f).obj G =>
        a.hom.app (op U)) hα
    have hmap : gP ≫ Sₓ.map αP = aU ≫ gPush :=
      TopCat.Presheaf.stalkFunctor_map_germ U (f z) hU αP
    have hpush : gPush ≫ p = gT := TopCat.Presheaf.stalkPushforward_germ (Type u) f T U z hU
    have hc : gQ ≫ m = cV ≫ gT :=
      TopCat.Presheaf.stalkFunctor_map_germ V z hzV cP
    have hu : gP ≫ eₛ.hom = uU ≫ gQ :=
      SchemeTheory.germ_sheafStalkPullbackIso_hom f H z U hU
    change gP ≫ (Sₓ.map αP ≫ p) = gP ≫ (eₛ.hom ≫ m)
    calc
      gP ≫ (Sₓ.map αP ≫ p) = (gP ≫ Sₓ.map αP) ≫ p := (Category.assoc _ _ _).symm
      _ = (aU ≫ gPush) ≫ p := congrArg (fun a => a ≫ p) hmap
      _ = aU ≫ gT := by rw [Category.assoc, hpush]
      _ = uU ≫ (cV ≫ gT) := by rw [haU, Category.assoc]
      _ = uU ≫ (gQ ≫ m) := congrArg (fun a => uU ≫ a) hc.symm
      _ = (uU ≫ gQ) ≫ m := (Category.assoc _ _ _).symm
      _ = (gP ≫ eₛ.hom) ≫ m := congrArg (fun a => a ≫ m) hu.symm
      _ = gP ≫ (eₛ.hom ≫ m) := Category.assoc _ _ _
  let BP : TX.Presheaf (Type u) := B.obj
  let mη : P ⟶ BP := ((etaleModuleZariskiRestriction X Λ).map η).hom
  let me : BP ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj T := e.hom.hom
  let mηS : P.stalk (f z) ⟶ BP.stalk (f z) := Sₓ.map mη
  let meS : BP.stalk (f z) ⟶
      ((TopCat.Presheaf.pushforward (Type u) f).obj T).stalk (f z) := Sₓ.map me
  have hmη : Mono mηS := etaleClosedUnit_zariskiStalk_mono i Λ F z
  have hmeIso : IsIso meS :=
    (Sₓ.mapIso ((sheafToPresheaf JX (Type u)).mapIso e)).isIso_hom
  have hme : Mono meS := inferInstance
  have hmap : Sₓ.map αP = mηS ≫ meS := Sₓ.map_comp mη me
  have hαMono : Mono (Sₓ.map αP) := hmap.symm ▸ mono_comp' hmη hme
  have hpIso : IsIso p :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing (Type u)
      i.isClosedEmbedding.isEmbedding.isInducing T z
  have hp : Mono p := inferInstance
  have hboth : Mono (Sₓ.map αP ≫ p) := mono_comp' hαMono hp
  have hcomp : Mono (eₛ.hom ≫ m) := heq ▸ hboth
  have hinv : Mono eₛ.inv := inferInstance
  have hfinal : Mono (eₛ.inv ≫ (eₛ.hom ≫ m)) := mono_comp' hinv hcomp
  have hcancel : eₛ.inv ≫ (eₛ.hom ≫ m) = m := eₛ.inv_hom_id_assoc m
  change Mono m
  exact hcancel ▸ hfinal

end EtaleCohomology
