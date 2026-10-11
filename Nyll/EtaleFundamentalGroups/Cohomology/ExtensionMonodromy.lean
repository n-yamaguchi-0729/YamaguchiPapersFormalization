/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.FiberTranslation
import Nyll.EtaleFundamentalGroups.Cohomology.FiberMap
import Nyll.EtaleFundamentalGroups.Cohomology.FiberCoefficientMap
import Nyll.EtaleFundamentalGroups.Cohomology.LocalTrivialization
import Nyll.EtaleFundamentalGroups.Cohomology.StalkFiber
import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacter
import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacterNaturality
import Nyll.EtaleCohomology.Constructible.Monodromy
import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.Topology.Category.FinTopCat

/-!
# Characters of actual étale extensions

The actual geometric monodromy of the finite locally constant sheaf of lifts
commutes with constant coefficient translations. Its geometric fiber is a
torsor for those coefficients, so displacement defines a continuous character
of the étale fundamental group. No monodromy or comparison property is added
as an assumption on the extension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X] (A : AddCommGrpCat.{u}) [Finite A]
  {E Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ Q) (h : i ≫ p = 0) (hs : (ShortComplex.mk i p h).ShortExact)
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ Q.obj ⋙ forget AddCommGrpCat.{u})
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

private abbrev liftSheaf : EtaleFiniteLocallyConstantSetSheaf X :=
  ⟨extensionFiber (ShortComplex.mk i p h) t,
    extensionFiber_isFiniteLocallyConstant (ShortComplex.mk i p h) t hs
      (constantAbelian_isFiniteLocallyConstant X A)⟩

/-- The continuous geometric action on the finite sheaf of quotient lifts. -/
abbrev extensionMonodromy : ContAction FintypeCat.{u} (Aut (FiniteEtale.fiber ξ)) :=
  (finiteLocallyConstantSetMonodromy ξ).functor.obj (liftSheaf A i p h hs t)

private def monodromyFiberEquiv :
    (extensionMonodromy A i p h hs t ξ).obj.V ≃
      abelianExtensionFiber
        ((ShortComplex.mk i p h).map (Scheme.pointSmallEtale ξ).sheafFiber)
        (quotientSectionStalk (ShortComplex.mk i p h) t ξ) :=
  ((finiteLocallyConstantSetMonodromyStalkIso ξ).app (liftSheaf A i p h hs t)).toEquiv.trans
    (extensionFiberStalkEquiv (ShortComplex.mk i p h) t ξ)

/-- The monodromy carrier is a torsor for the original coefficient group. -/
@[instance_reducible]
def extensionMonodromyTorsor :
    Torsor (Multiplicative A) (extensionMonodromy A i p h hs t ξ).obj.V :=
  extensionFiberTransportTorsor
    ((ShortComplex.mk i p h).map (Scheme.pointSmallEtale ξ).sheafFiber)
    (shortExact_geometricStalk ξ _ hs) _ A (constantAbelianStalkIso ξ A).symm
    (monodromyFiberEquiv A i p h hs t ξ)

private abbrev translationMorphism (a : A) :
    liftSheaf A i p h hs t ⟶ liftSheaf A i p h hs t :=
  ObjectProperty.homMk (constantFiberTranslation A i p h t a)

theorem translation_on_monodromy (a : A)
    (q : (extensionMonodromy A i p h hs t ξ).obj.V) :
    let := extensionMonodromyTorsor A i p h hs t ξ
    ((finiteLocallyConstantSetMonodromy ξ).functor.map
      (translationMorphism A i p h hs t a)).hom.hom q = Multiplicative.ofAdd a • q := by
  let T := extensionMonodromyTorsor A i p h hs t ξ
  let e := monodromyFiberEquiv A i p h hs t ξ
  let I := finiteLocallyConstantSetMonodromyStalkIso ξ
  let F := liftSheaf A i p h hs t
  let f := translationMorphism A i p h hs t a
  apply e.injective
  apply Subtype.ext
  have hn := ConcreteCategory.congr_hom (I.hom.naturality f) q
  have hn' := congrArg (fun z =>
    (extensionFiberStalkEquiv (ShortComplex.mk i p h) t ξ z).val) hn
  exact hn'.trans ((constantFiberTranslation_stalk A i p h t ξ a (I.hom.app F q)).trans
    (extensionFiberTransportTorsor_smul _ (shortExact_geometricStalk ξ _ hs) _ A
      (constantAbelianStalkIso ξ A).symm e (Multiplicative.ofAdd a) q).symm)

/-- Monodromy commutes with coefficient translations because these are
morphisms of the actual finite locally constant sheaf. -/
theorem extensionMonodromy_commutes :
    let := extensionMonodromyTorsor A i p h hs t ξ
    SMulCommClass (Aut (FiniteEtale.fiber ξ)) (Multiplicative A)
      (extensionMonodromy A i p h hs t ξ).obj.V := by
  let T := extensionMonodromyTorsor A i p h hs t ξ
  constructor
  intro g a q
  let f := (finiteLocallyConstantSetMonodromy ξ).functor.map
    (translationMorphism A i p h hs t a.toAdd)
  have hf := ConcreteCategory.congr_hom (f.hom.comm g) q
  change f.hom.hom (g • q) = g • f.hom.hom q at hf
  rw [translation_on_monodromy A i p h hs t ξ,
    translation_on_monodromy A i p h hs t ξ] at hf
  exact hf.symm

/-- The continuous character obtained from the actual geometric monodromy of
an abelian étale extension. The coefficient group has its discrete topology. -/
def extensionMonodromyCharacter :
    let : TopologicalSpace (Multiplicative A) := ⊥
    Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  let T := extensionMonodromyTorsor A i p h hs t ξ
  have := extensionMonodromy_commutes A i p h hs t ξ
  let M := extensionMonodromy A i p h hs t ξ
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) M.obj.V := M.property
  exact torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) (Classical.choice T.nonempty)

/-- Changing the geometric base point transports the character along the actual
isomorphism of fiber functors. Naturality of the represented lift sheaf proves
compatibility with both monodromy and coefficient translation. -/
theorem extensionMonodromyCharacter_basePoint
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (η : Spec (.of Ω') ⟶ X)
    (τ : FiniteEtale.fiber ξ ≅ FiniteEtale.fiber η) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    (extensionMonodromyCharacter A i p h hs t η).comp
      (ContinuousMonoidHom.toContinuousMonoidHom
        (PreGaloisCategory.continuousConjAut τ)) =
      extensionMonodromyCharacter A i p h hs t ξ := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  let T := extensionMonodromyTorsor A i p h hs t ξ
  let T' := extensionMonodromyTorsor A i p h hs t η
  have := extensionMonodromy_commutes A i p h hs t ξ
  have := extensionMonodromy_commutes A i p h hs t η
  let M := extensionMonodromy A i p h hs t ξ
  let M' := extensionMonodromy A i p h hs t η
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) M.obj.V := M.property
  have : ContinuousSMul (Aut (FiniteEtale.fiber η)) M'.obj.V := M'.property
  let D : EtaleFiniteLocallyConstantSetSheaf X ⥤ FiniteEtale X :=
    (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse
  let V : FiniteEtale X := D.obj (liftSheaf A i p h hs t)
  let f : M.obj.V → M'.obj.V := τ.hom.app V
  have hcoeff (a : Multiplicative A) (q : M.obj.V) : f (a • q) = a • f q := by
    let m := translationMorphism A i p h hs t a.toAdd
    have hn := ConcreteCategory.congr_hom (τ.hom.naturality (D.map m)) q
    change f (((finiteLocallyConstantSetMonodromy ξ).functor.map m).hom.hom q) =
      ((finiteLocallyConstantSetMonodromy η).functor.map m).hom.hom (f q) at hn
    rw [translation_on_monodromy A i p h hs t ξ,
      translation_on_monodromy A i p h hs t η] at hn
    exact hn
  have hgroup (g : Aut (FiniteEtale.fiber ξ)) (q : M.obj.V) :
      f (g • q) = PreGaloisCategory.continuousConjAut τ g • f q :=
    ConcreteCategory.congr_hom
      (((PreGaloisCategory.functorToContActionFiberIso τ).hom.app V).hom.comm g) q
  let q : M.obj.V := Classical.choice T.nonempty
  let q' : M'.obj.V := Classical.choice T'.nonempty
  apply ContinuousMonoidHom.ext
  intro g
  change torsorCharacter (G := Aut (FiniteEtale.fiber η)) q'
      (PreGaloisCategory.continuousConjAut τ g) =
    torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) q g
  rw [torsorCharacter_eq q' (f q)]
  change ((PreGaloisCategory.continuousConjAut τ g • f q) /ₛ f q :
    Multiplicative A) = (g • q) /ₛ q
  rw [← hgroup]
  have he := hcoeff ((g • q) /ₛ q) q
  rw [sdiv_smul] at he
  exact (congrArg (· /ₛ f q) he).trans (smul_sdiv _ _)

/-- A comparison that is the identity on the kernel and quotient preserves
the continuous monodromy character of the actual lift sheaf. -/
theorem extensionMonodromyCharacter_eq_of_comparison
    {E' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (i' : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E')
    (p' : E' ⟶ Q) (h' : i' ≫ p' = 0) (hs' : (ShortComplex.mk i' p' h').ShortExact)
    (f : E ⟶ E') (hi : i ≫ f = i') (hp : f ≫ p' = p) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    extensionMonodromyCharacter A i p h hs t ξ =
      extensionMonodromyCharacter A i' p' h' hs' t ξ := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  let T := extensionMonodromyTorsor A i p h hs t ξ
  let T' := extensionMonodromyTorsor A i' p' h' hs' t ξ
  have := extensionMonodromy_commutes A i p h hs t ξ
  have := extensionMonodromy_commutes A i' p' h' hs' t ξ
  let M := (finiteLocallyConstantSetMonodromy ξ).functor
  let F := liftSheaf A i p h hs t
  let F' := liftSheaf A i' p' h' hs' t
  let mf : F ⟶ F' := ObjectProperty.homMk
    (extensionFiberMap i p h i' p' h' f hp t)
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) (M.obj F).obj.V := (M.obj F).property
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) (M.obj F').obj.V := (M.obj F').property
  have hcoeff (a : Multiplicative A) (q : (M.obj F).obj.V) :
      (M.map mf).hom.hom (a • q) = a • (M.map mf).hom.hom q := by
    have hsquare : translationMorphism A i p h hs t a.toAdd ≫ mf =
        mf ≫ translationMorphism A i' p' h' hs' t a.toAdd :=
      ObjectProperty.hom_ext _
        (extensionFiberMap_translation A i p h i' p' h' f hi hp t a.toAdd)
    have hn := congrArg M.map hsquare
    rw [M.map_comp, M.map_comp] at hn
    have hv := congrArg
      (fun k : M.obj F ⟶ M.obj F' => k.hom.hom q) hn
    change (M.map mf).hom.hom
        ((M.map (translationMorphism A i p h hs t a.toAdd)).hom.hom q) =
      (M.map (translationMorphism A i' p' h' hs' t a.toAdd)).hom.hom
        ((M.map mf).hom.hom q) at hv
    rw [translation_on_monodromy A i p h hs t ξ,
      translation_on_monodromy A i' p' h' hs' t ξ] at hv
    exact hv
  have hgroup (g : Aut (FiniteEtale.fiber ξ)) (q : (M.obj F).obj.V) :
      (M.map mf).hom.hom (g • q) = g • (M.map mf).hom.hom q :=
    ConcreteCategory.congr_hom ((M.map mf).hom.comm g) q
  change torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) (Classical.choice T.nonempty) =
    torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) (Classical.choice T'.nonempty)
  exact (torsorCharacter_map (M.map mf).hom.hom hcoeff hgroup _).trans
    (torsorCharacter_eq _ _)

/-- Changing finite constant coefficients sends the character to its image
under the original coefficient homomorphism. The comparison uses the actual
morphism of extensions, not a separate compatibility assumption on monodromy. -/
theorem extensionMonodromyCharacter_changeCoefficients
    (B : AddCommGrpCat.{u}) [Finite B] (α : A ⟶ B)
    {E' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (i' : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj B ⟶ E')
    (p' : E' ⟶ Q) (h' : i' ≫ p' = 0) (hs' : (ShortComplex.mk i' p' h').ShortExact)
    (f : E ⟶ E')
    (hi : i ≫ f = (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map α ≫ i')
    (hp : f ≫ p' = p) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : TopologicalSpace (Multiplicative B) := ⊥
    (discreteCoefficientHom α.hom).comp (extensionMonodromyCharacter A i p h hs t ξ) =
      extensionMonodromyCharacter B i' p' h' hs' t ξ := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  let : TopologicalSpace (Multiplicative B) := ⊥
  let T := extensionMonodromyTorsor A i p h hs t ξ
  let T' := extensionMonodromyTorsor B i' p' h' hs' t ξ
  have := extensionMonodromy_commutes A i p h hs t ξ
  have := extensionMonodromy_commutes B i' p' h' hs' t ξ
  let M := (finiteLocallyConstantSetMonodromy ξ).functor
  let F := liftSheaf A i p h hs t
  let F' := liftSheaf B i' p' h' hs' t
  let mf : F ⟶ F' := ObjectProperty.homMk
    (extensionFiberMap i p h i' p' h' f hp t)
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) (M.obj F).obj.V := (M.obj F).property
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) (M.obj F').obj.V := (M.obj F').property
  have hcoeff (a : Multiplicative A) (q : (M.obj F).obj.V) :
      (M.map mf).hom.hom (a • q) =
        (discreteCoefficientHom α.hom) a • (M.map mf).hom.hom q := by
    have hsquare : translationMorphism A i p h hs t a.toAdd ≫ mf =
        mf ≫ translationMorphism B i' p' h' hs' t (α a.toAdd) :=
      ObjectProperty.hom_ext _
        (extensionFiberMap_changeCoefficients α i p h i' p' h' f hi hp t a.toAdd)
    have hn := congrArg M.map hsquare
    rw [M.map_comp, M.map_comp] at hn
    have hv := congrArg (fun k : M.obj F ⟶ M.obj F' => k.hom.hom q) hn
    change (M.map mf).hom.hom
        ((M.map (translationMorphism A i p h hs t a.toAdd)).hom.hom q) =
      (M.map (translationMorphism B i' p' h' hs' t (α a.toAdd))).hom.hom
        ((M.map mf).hom.hom q) at hv
    rw [translation_on_monodromy A i p h hs t ξ,
      translation_on_monodromy B i' p' h' hs' t ξ] at hv
    exact hv
  have hgroup (g : Aut (FiniteEtale.fiber ξ)) (q : (M.obj F).obj.V) :
      (M.map mf).hom.hom (g • q) = g • (M.map mf).hom.hom q :=
    ConcreteCategory.congr_hom ((M.map mf).hom.comm g) q
  change (discreteCoefficientHom α.hom).comp
      (torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) (Classical.choice T.nonempty)) =
    torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) (Classical.choice T'.nonempty)
  exact (torsorCharacter_comp (discreteCoefficientHom α.hom)
    (M.map mf).hom.hom hcoeff hgroup _).trans (torsorCharacter_eq _ _)

end EtaleFundamentalGroups.Cohomology
