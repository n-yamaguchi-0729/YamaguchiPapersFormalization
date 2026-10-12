/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CohomologyPullback
import Nyll.JacobianVarieties.Kummer.CohomologyPullbackFibers
import Nyll.EtaleFundamentalGroups.Cohomology.MonodromyPullback
import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality

/-!
# Scheme-pullback naturality of the actual finite H¹ comparison

The actual inverse-image map on derived cohomology corresponds to precomposition
by the actual homomorphism of geometric fundamental groups. The proof uses the
inverse-image extension, the map of its lift sheaf, and the induced map of
finite étale representers. Both group actions are their original monodromy
actions; no cohomology comparison is assumed as input.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits EtaleCohomology
open EtaleFundamentalGroups.Cohomology
open scoped FintypeCatDiscrete

namespace JacobianVarieties.Kummer

private theorem torsorCharacter_map_hom
    {G H B P Q : Type*} [Group G] [Group H] [CommGroup B]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace B]
    [Torsor B P] [MulAction H P] [SMulCommClass H B P]
    [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul H P]
    [Torsor B Q] [MulAction G Q] [SMulCommClass G B Q]
    [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul G Q]
    (φ : G →ₜ* H) (m : P → Q)
    (hc : ∀ b : B, ∀ p : P, m (b • p) = b • m p)
    (hg : ∀ g : G, ∀ p : P, m (φ g • p) = g • m p) (p : P) :
    (torsorCharacter (G := H) p).comp φ = torsorCharacter (G := G) (m p) := by
  apply ContinuousMonoidHom.ext
  intro g
  change ((φ g • p) /ₛ p : B) = (g • m p) /ₛ m p
  calc
    ((φ g • p) /ₛ p : B) = (((φ g • p) /ₛ p) • m p) /ₛ m p :=
      (smul_sdiv _ _).symm
    _ = m ((((φ g • p) /ₛ p) : B) • p) /ₛ m p :=
      congrArg (· /ₛ m p) (hc _ p).symm
    _ = (g • m p) /ₛ m p := by rw [sdiv_smul, hg]

private abbrev lifts {Z : Scheme.{u}} (A : AddCommGrpCat.{u}) [Finite A]
    {E Q : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}}
    (i : (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
    (p : E ⟶ Q) (h : i ≫ p = 0) (hs : (ShortComplex.mk i p h).ShortExact)
    (t : (Functor.const Z.Etaleᵒᵖ).obj PUnit ⟶ Q.obj ⋙ forget AddCommGrpCat.{u}) :
    EtaleFiniteLocallyConstantSetSheaf Z :=
  ⟨extensionFiber (ShortComplex.mk i p h) t,
    extensionFiber_isFiniteLocallyConstant (ShortComplex.mk i p h) t hs
      (constantAbelian_isFiniteLocallyConstant Z A)⟩

private theorem translation_on_monodromy
    {Z : Scheme.{u}} [ConnectedSpace Z] (A : AddCommGrpCat.{u}) [Finite A]
    {E Q : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}}
    (i : (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
    (p : E ⟶ Q) (h : i ≫ p = 0) (hs : (ShortComplex.mk i p h).ShortExact)
    (t : (Functor.const Z.Etaleᵒᵖ).obj PUnit ⟶ Q.obj ⋙ forget AddCommGrpCat.{u})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ Z)
    (a : A) (q : (extensionMonodromy A i p h hs t ζ).obj.V) :
    let := extensionMonodromyTorsor A i p h hs t ζ
    ((finiteLocallyConstantSetMonodromy ζ).functor.map
      (ObjectProperty.homMk (P := IsEtaleFiniteLocallyConstantSet (X := Z))
        (constantFiberTranslation A i p h t a) :
          lifts A i p h hs t ⟶ lifts A i p h hs t)).hom.hom q =
      Multiplicative.ofAdd a • q := by
  let T := extensionMonodromyTorsor A i p h hs t ζ
  let e : (extensionMonodromy A i p h hs t ζ).obj.V ≃
      abelianExtensionFiber ((ShortComplex.mk i p h).map
        (Scheme.pointSmallEtale ζ).sheafFiber)
        (quotientSectionStalk (ShortComplex.mk i p h) t ζ) :=
    ((finiteLocallyConstantSetMonodromyStalkIso ζ).app (lifts A i p h hs t)).toEquiv.trans
      (extensionFiberStalkEquiv (ShortComplex.mk i p h) t ζ)
  let I := finiteLocallyConstantSetMonodromyStalkIso ζ
  let F := lifts A i p h hs t
  let aF : F ⟶ F := ObjectProperty.homMk (constantFiberTranslation A i p h t a)
  apply e.injective
  apply Subtype.ext
  have hn := ConcreteCategory.congr_hom (I.hom.naturality aF) q
  have hn' := congrArg (fun z =>
    (extensionFiberStalkEquiv (ShortComplex.mk i p h) t ζ z).val) hn
  exact hn'.trans ((constantFiberTranslation_stalk A i p h t ζ a (I.hom.app F q)).trans
    (extensionFiberTransportTorsor_smul _ (shortExact_geometricStalk ζ _ hs) _ A
      (constantAbelianStalkIso ζ A).symm e (Multiplicative.ofAdd a) q).symm)

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
  (f : X ⟶ Y) (A : AddCommGrpCat.{u}) [Finite A]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The character of the actual inverse-image extension is the original
character precomposed with the scheme-induced fundamental group map. -/
theorem extensionMonodromyCharacter_pullback
    {E : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
    (i : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
    (p : E ⟶ (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (h : i ≫ p = 0)
    (hs : (ShortComplex.mk i p h).ShortExact) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    extensionMonodromyCharacter A (pullbackExtension f A i p h).f
        (pullbackExtension f A i p h).g (pullbackExtension f A i p h).zero
        (pullbackExtension_shortExact f A i p h hs) (integerUnitSection X) ξ =
      (extensionMonodromyCharacter A i p h hs (integerUnitSection Y) (ξ ≫ f)).comp
        (FiniteEtale.fundamentalGroupHom f ξ) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  let S := pullbackExtension f A i p h
  have hS : S.ShortExact := pullbackExtension_shortExact f A i p h hs
  let TY := extensionMonodromyTorsor A i p h hs (integerUnitSection Y) (ξ ≫ f)
  let TX := extensionMonodromyTorsor A S.f S.g S.zero hS (integerUnitSection X) ξ
  have := extensionMonodromy_commutes A i p h hs (integerUnitSection Y) (ξ ≫ f)
  have := extensionMonodromy_commutes A S.f S.g S.zero hS (integerUnitSection X) ξ
  let FY := lifts A i p h hs (integerUnitSection Y)
  let FX := lifts A S.f S.g S.zero hS (integerUnitSection X)
  let MY := (finiteLocallyConstantSetMonodromy (ξ ≫ f)).functor
  let MX := (finiteLocallyConstantSetMonodromy ξ).functor
  have : ContinuousSMul (Aut (FiniteEtale.fiber (ξ ≫ f))) (MY.obj FY).obj.V :=
    (MY.obj FY).property
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) (MX.obj FX).obj.V :=
    (MX.obj FX).property
  let α : FY.obj ⟶ (etaleSetPushforward f).obj FX.obj := pullbackExtensionFiberMap f A i p h
  let m : (MY.obj FY).obj.V → (MX.obj FX).obj.V :=
    finiteLocallyConstantMonodromyPullbackMap f ξ FY FX α
  have hc (a : Multiplicative A) (q : (MY.obj FY).obj.V) : m (a • q) = a • m q := by
    let aY : FY ⟶ FY :=
      ObjectProperty.homMk (constantFiberTranslation A i p h (integerUnitSection Y) a.toAdd)
    let aX : FX ⟶ FX := ObjectProperty.homMk
      (constantFiberTranslation A S.f S.g S.zero (integerUnitSection X) a.toAdd)
    have hn := finiteLocallyConstantMonodromyPullbackMap_naturality f ξ FY FX α aY aX
      (pullbackExtensionFiberMap_translation f A i p h a.toAdd) q
    have hY := translation_on_monodromy A i p h hs (integerUnitSection Y) (ξ ≫ f) a.toAdd q
    have hX := translation_on_monodromy A S.f S.g S.zero hS (integerUnitSection X) ξ
      a.toAdd (m q)
    exact (congrArg m hY.symm).trans (hn.trans hX)
  have hg (g : Aut (FiniteEtale.fiber ξ)) (q : (MY.obj FY).obj.V) :
      m ((FiniteEtale.fundamentalGroupHom f ξ g) • q) = g • m q :=
    finiteLocallyConstantMonodromyPullbackMap_smul f ξ FY FX α g q
  let q := Classical.choice TY.nonempty
  let r := Classical.choice TX.nonempty
  change torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) r =
    (torsorCharacter (G := Aut (FiniteEtale.fiber (ξ ≫ f))) q).comp
      (FiniteEtale.fundamentalGroupHom f ξ)
  exact (torsorCharacter_eq r (m q)).trans
    (torsorCharacter_map_hom (FiniteEtale.fundamentalGroupHom f ξ) m hc hg q).symm

/-- Actual derived H¹ pullback corresponds to precomposition of characters
by the actual homomorphism of geometric fundamental groups. -/
theorem h1Character_constantCohomologyPullback
    (a : Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    h1Character A ξ (constantCohomologyPullback f A 1 a) =
      (h1Character A (ξ ≫ f) a).comp (FiniteEtale.fundamentalGroupHom f ξ) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  obtain ⟨E, i, p, h, hs, ha⟩ := exists_h1_extension Y _ a
  rw [← ha, constantCohomologyPullback_extClass f A i p h hs,
    h1Character_extClass, h1Character_extClass]
  exact extensionMonodromyCharacter_pullback f A ξ i p h hs

/-- Scheme-morphism naturality of the existing finite H¹ equivalence. The
cohomology map is the actual exact inverse image on Ext, and the character map
uses the actual geometric-fiber functor homomorphism. -/
theorem finiteH1CharacterEquiv_schemePullback
    (a : Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    (finiteH1CharacterEquiv A ξ (constantCohomologyPullback f A 1 a)).toMul =
      (finiteH1CharacterEquiv A (ξ ≫ f) a).toMul.comp
        (FiniteEtale.fundamentalGroupHom f ξ) :=
  h1Character_constantCohomologyPullback f A ξ a

end JacobianVarieties.Kummer
