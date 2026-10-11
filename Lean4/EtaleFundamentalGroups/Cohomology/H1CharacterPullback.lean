/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.FiberPullbackTranslation
import EtaleFundamentalGroups.Cohomology.RepresenterPullback
import EtaleFundamentalGroups.Cohomology.H1Character

/-!
# Geometric naturality of the actual étale H¹ character

The finite lift cover of the actual inverse-image extension is the geometric
pullback of the original cover. Its comparison preserves original coefficient
translations. Naturality of finite-cover monodromy therefore identifies the
derived H¹ pullback with precomposition by the actual fundamental-group map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
  (f : X ⟶ Y) (A : AddCommGrpCat.{u}) [Finite A]
  {E : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))
  (h : i ≫ p = 0) (hs : (ShortComplex.mk i p h).ShortExact)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The continuous extension character commutes with actual scheme pullback. -/
theorem extensionMonodromyCharacter_schemePullback :
    let : TopologicalSpace (Multiplicative A) := ⊥
    (extensionMonodromyCharacter A i p h hs (integerUnitSection Y) (ξ ≫ f)).comp
        (FiniteEtale.fundamentalGroupHom f ξ) =
      extensionMonodromyCharacter A (schemePullbackH1Extension f A i p h).f
        (schemePullbackH1Extension f A i p h).g
        (schemePullbackH1Extension f A i p h).zero
        (schemePullbackH1Extension_shortExact f A i p h hs)
        (integerUnitSection X) ξ := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  let S' := schemePullbackH1Extension f A i p h
  let hs' := schemePullbackH1Extension_shortExact f A i p h hs
  let SY : EtaleFiniteLocallyConstantSetSheaf Y :=
    ⟨extensionFiber (ShortComplex.mk i p h) (integerUnitSection Y),
      extensionFiber_isFiniteLocallyConstant (ShortComplex.mk i p h)
        (integerUnitSection Y) hs (constantAbelian_isFiniteLocallyConstant Y A)⟩
  let SX : EtaleFiniteLocallyConstantSetSheaf X :=
    ⟨extensionFiber S' (integerUnitSection X),
      extensionFiber_isFiniteLocallyConstant S' (integerUnitSection X) hs'
        (constantAbelian_isFiniteLocallyConstant X A)⟩
  let NX := (finiteLocallyConstantSetMonodromy ξ).functor
  let NY := (finiteLocallyConstantSetMonodromy (ξ ≫ f)).functor
  let L := finiteLocallyConstantSetPullback f
  let R := ContAction.res FintypeCat (FiniteEtale.fundamentalGroupHom f ξ)
  let I := finiteLocallyConstantSetMonodromyPullbackIso f ξ
  let e : L.obj SY ≅ SX :=
    ObjectProperty.isoMk _ (schemePullbackH1Extension_fiberIso f A i p h)
  let b : NX.obj SX ≅ R.obj (NY.obj SY) :=
    (NX.mapIso e).symm ≪≫ I.app SY
  let TX := extensionMonodromyTorsor A S'.f S'.g S'.zero hs' (integerUnitSection X) ξ
  let TY := extensionMonodromyTorsor A i p h hs (integerUnitSection Y) (ξ ≫ f)
  have := extensionMonodromy_commutes A S'.f S'.g S'.zero hs'
    (integerUnitSection X) ξ
  have := extensionMonodromy_commutes A i p h hs (integerUnitSection Y) (ξ ≫ f)
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) (NX.obj SX).obj.V :=
    (NX.obj SX).property
  have : ContinuousSMul (Aut (FiniteEtale.fiber (ξ ≫ f))) (NY.obj SY).obj.V :=
    (NY.obj SY).property
  let bfun : (NX.obj SX).obj.V → (NY.obj SY).obj.V := b.hom.hom.hom
  have hcoeff (a : Multiplicative A) (q : (NX.obj SX).obj.V) :
      bfun (a • q) = a • bfun q := by
    let δY : SY ⟶ SY := ObjectProperty.homMk
      (constantFiberTranslation A i p h (integerUnitSection Y) a.toAdd)
    let δX : SX ⟶ SX := ObjectProperty.homMk
      (constantFiberTranslation A S'.f S'.g S'.zero (integerUnitSection X) a.toAdd)
    have he : L.map δY ≫ e.hom = e.hom ≫ δX :=
      ObjectProperty.hom_ext _
        (schemePullbackH1Extension_fiberIso_translation f A i p h a.toAdd)
    have hei : δX ≫ e.inv = e.inv ≫ L.map δY := by
      apply (cancel_mono e.hom).1
      calc
        (δX ≫ e.inv) ≫ e.hom = δX := by
          rw [Category.assoc, e.inv_hom_id, Category.comp_id]
        _ = (e.inv ≫ L.map δY) ≫ e.hom := by
          rw [Category.assoc, he, e.inv_hom_id_assoc]
    have hn := congrArg NX.map hei
    rw [NX.map_comp, NX.map_comp] at hn
    have hi : NX.map (L.map δY) ≫ I.hom.app SY =
        I.hom.app SY ≫ R.map (NY.map δY) := I.hom.naturality δY
    have hb : NX.map δX ≫ b.hom = b.hom ≫ R.map (NY.map δY) := by
      change NX.map δX ≫ (NX.map e.inv ≫ I.hom.app SY) =
        (NX.map e.inv ≫ I.hom.app SY) ≫ R.map (NY.map δY)
      calc
        NX.map δX ≫ (NX.map e.inv ≫ I.hom.app SY) =
            (NX.map δX ≫ NX.map e.inv) ≫ I.hom.app SY :=
          (Category.assoc _ _ _).symm
        _ = (NX.map e.inv ≫ NX.map (L.map δY)) ≫ I.hom.app SY :=
          congrArg (fun k => k ≫ I.hom.app SY) hn
        _ = (NX.map e.inv ≫ I.hom.app SY) ≫ R.map (NY.map δY) := by
          rw [Category.assoc, hi, ← Category.assoc]
    have hv := congrArg
      (fun k : NX.obj SX ⟶ R.obj (NY.obj SY) => k.hom.hom q) hb
    change bfun ((NX.map δX).hom.hom q) = (NY.map δY).hom.hom (bfun q) at hv
    have hx := translation_on_monodromy A S'.f S'.g S'.zero hs'
      (integerUnitSection X) ξ a.toAdd q
    have hy := translation_on_monodromy A i p h hs (integerUnitSection Y)
      (ξ ≫ f) a.toAdd (bfun q)
    exact (congrArg bfun hx).symm.trans (hv.trans hy)
  have hgroup (g : Aut (FiniteEtale.fiber ξ)) (q : (NX.obj SX).obj.V) :
      bfun (g • q) = FiniteEtale.fundamentalGroupHom f ξ g • bfun q :=
    ConcreteCategory.congr_hom (b.hom.hom.comm g) q
  let qX : (NX.obj SX).obj.V := Classical.choice TX.nonempty
  let qY : (NY.obj SY).obj.V := Classical.choice TY.nonempty
  apply ContinuousMonoidHom.ext
  intro g
  change torsorCharacter (G := Aut (FiniteEtale.fiber (ξ ≫ f))) qY
      (FiniteEtale.fundamentalGroupHom f ξ g) =
    torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) qX g
  rw [torsorCharacter_eq qY (bfun qX)]
  change ((FiniteEtale.fundamentalGroupHom f ξ g • bfun qX) /ₛ bfun qX :
    Multiplicative A) = (g • qX) /ₛ qX
  rw [← hgroup]
  have he := hcoeff ((g • qX) /ₛ qX) qX
  rw [sdiv_smul] at he
  exact (congrArg (· /ₛ bfun qX) he).trans (smul_sdiv _ _)

/-- The original character equivalence from actual derived H¹ is natural under
arbitrary scheme morphisms between connected schemes. -/
theorem h1Character_schemePullback
    (a : Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    (h1Character A (ξ ≫ f) a).comp (FiniteEtale.fundamentalGroupHom f ξ) =
      h1Character A ξ (constantCohomologyPullback f A 1 a) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  obtain ⟨E, i, p, h, hs, ha⟩ := exists_h1_extension Y _ a
  let S' := schemePullbackH1Extension f A i p h
  let hs' := schemePullbackH1Extension_shortExact f A i p h hs
  have hy := h1Character_extClass A (ξ ≫ f) i p h hs
  rw [ha] at hy
  have hx := h1Character_extClass A ξ S'.f S'.g S'.zero hs'
  have he : constantCohomologyPullback f A 1 a = hs'.extClass := by
    rw [← ha]
    exact constantCohomologyPullback_extClass f A i p h hs
  change (h1Character A (ξ ≫ f) a).comp (FiniteEtale.fundamentalGroupHom f ξ) =
    h1Character A ξ (constantCohomologyPullback f A 1 a)
  exact (congrArg
    (fun c : Aut (FiniteEtale.fiber (ξ ≫ f)) →ₜ* Multiplicative A =>
      c.comp (FiniteEtale.fundamentalGroupHom f ξ)) hy).trans
    ((extensionMonodromyCharacter_schemePullback f A i p h hs ξ).trans
      (hx.symm.trans (congrArg (fun c => h1Character A ξ c) he.symm)))

end EtaleFundamentalGroups.Cohomology
