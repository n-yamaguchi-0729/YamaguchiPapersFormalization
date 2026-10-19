/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
/-
The following notice applies only to the NYLL proof completions and additions,
not to the upstream declarations and adapted code credited above.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
/-
Upstream declaration and adaptation reference (historical copy revision unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Point.lean

The referenced upstream file leaves the constructions and proofs for
fiberObjEquivHom, its naturality lemmas, fiberIsoCoyoneda,
isField_of_isConnected, ContinuousSMul, and isGalois_of_isGalois unfinished.
Their implementations here are NYLL proof completions. The dependent fiber action
and final fundamental-group construction retain the current IsSepClosed and
IsSepClosure assumptions and the corresponding NYLL repairs. The independent
upstream-derived field-point API is in Pi1.GeometricFiber.FieldPoints.
-/

module

public import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
public import Nyll.EtaleFundamentalGroups.Pi1.GeometricFiber.FieldPoints
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry

/-!
# Geometric fibers and field-valued points

This module identifies geometric fibers of finite étale schemes with morphisms
from the field point and with algebra homomorphisms from their section rings.
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory


namespace AlgebraicGeometry

namespace FiniteEtale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  («ξ» : Spec (.of Ω) ⟶ S)

/-- Identify points of the finite etale fiber with morphisms from the field point in the over
category. -/
noncomputable
def fiberObjEquivHom (X : FiniteEtale S) : (fiber «ξ»).obj X ≃ (Over.mk «ξ» ⟶ X.toComma) := by
  let baseIso : (Over.mk «ξ»).left ≅ Spec (.of Ω) :=
    eqToIso (Over.mk_left «ξ»)
  let : IsFiniteEtale baseIso.hom := by constructor
  let T : FiniteEtale (Spec (.of Ω)) := FiniteEtale.mk baseIso.hom
  have baseIso_hom_comp : baseIso.hom ≫ «ξ» = (Over.mk «ξ»).hom := by
    change eqToHom (Over.mk_left «ξ») ≫ «ξ» = (Over.mk «ξ»).hom
    exact eq_of_heq (eqToHom_comp_heq «ξ» (Over.mk_left «ξ»))
  let t : T.left := by
    exact baseIso.inv.base
      (Classical.choice (inferInstance : Nonempty (Spec (.of Ω))))
  let pointHom (x : (fiber «ξ»).obj X) : T ⟶ (pullback «ξ»).obj X :=
    (forgetScheme Ω).preimage (FintypeCat.homMk fun _ ↦ x)
  let sourceMap (x : Over.mk «ξ» ⟶ X.toComma) : T.left ⟶ X.left := x.left
  let liftHom (x : Over.mk «ξ» ⟶ X.toComma) : T ⟶ (pullback «ξ»).obj X :=
    MorphismProperty.Over.homMk
      (Limits.pullback.lift (sourceMap x) T.hom (by
        change x.left ≫ X.toComma.hom = baseIso.hom ≫ «ξ»
        exact x.w.trans baseIso_hom_comp.symm))
      (Limits.pullback.lift_snd _ _ _)
  let toOver (x : (fiber «ξ»).obj X) : Over.mk «ξ» ⟶ X.toComma :=
    Over.homMk ((pointHom x).left ≫ Limits.pullback.fst X.hom «ξ») (by
      have hpoint :
          (pointHom x).left ≫ Limits.pullback.snd X.hom «ξ» =
            baseIso.hom := by
        have hp := (pointHom x).w
        change (pointHom x).left ≫ Limits.pullback.snd X.hom «ξ» =
          baseIso.hom at hp
        exact hp
      have hcondition :
          ((pointHom x).left ≫ Limits.pullback.fst X.hom «ξ») ≫ X.toComma.hom =
            ((pointHom x).left ≫ Limits.pullback.snd X.hom «ξ») ≫ «ξ» := by
        calc
          ((pointHom x).left ≫ Limits.pullback.fst X.hom «ξ») ≫ X.toComma.hom =
              (pointHom x).left ≫
                (Limits.pullback.fst X.hom «ξ» ≫ X.hom) := Category.assoc _ _ _
          _ = (pointHom x).left ≫
                (Limits.pullback.snd X.hom «ξ» ≫ «ξ») :=
              congrArg (fun q ↦ (pointHom x).left ≫ q)
                Limits.pullback.condition
          _ = ((pointHom x).left ≫ Limits.pullback.snd X.hom «ξ») ≫ «ξ» :=
                (Category.assoc _ _ _).symm
      have hpoint_comp :
          ((pointHom x).left ≫ Limits.pullback.snd X.hom «ξ») ≫ «ξ» =
            baseIso.hom ≫ «ξ» :=
        congrArg (fun q ↦ q ≫ «ξ») hpoint
      exact hcondition.trans (hpoint_comp.trans baseIso_hom_comp))
  let fromOver (x : Over.mk «ξ» ⟶ X.toComma) : (fiber «ξ»).obj X :=
    (forgetScheme Ω).map (liftHom x) t
  let : Subsingleton T.left := by
    constructor
    intro a b
    apply baseIso.hom.homeomorph.injective
    exact Subsingleton.elim _ _
  let : Subsingleton ((forgetScheme Ω).obj T) := by
    change Subsingleton T.left
    infer_instance
  refine ⟨toOver, fromOver, ?_, ?_⟩
  · intro x
    have h : liftHom (toOver x) = pointHom x := by
      apply MorphismProperty.Over.Hom.ext
      apply Limits.pullback.hom_ext
      · change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst X.hom «ξ» =
          (pointHom x).left ≫ Limits.pullback.fst X.hom «ξ»
        rw [Limits.pullback.lift_fst]
        rfl
      · change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd X.hom «ξ» =
          (pointHom x).left ≫ Limits.pullback.snd X.hom «ξ»
        rw [Limits.pullback.lift_snd]
        symm
        have hp := (pointHom x).w
        change (pointHom x).left ≫ Limits.pullback.snd X.hom «ξ» =
          T.hom at hp
        exact hp
    change (forgetScheme Ω).map (liftHom (toOver x)) t = x
    rw [h]
    simp only [pointHom, Functor.map_preimage]
    rfl
  · intro x
    have h : pointHom (fromOver x) = liftHom x := by
      apply (forgetScheme Ω).map_injective
      ext z
      rw [Subsingleton.elim z t]
      simp only [pointHom, fromOver, Functor.map_preimage]
      rfl
    ext1
    change (pointHom (fromOver x)).left ≫ Limits.pullback.fst X.hom «ξ» = x.left
    rw [h]
    change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst X.hom «ξ» = x.left
    exact Limits.pullback.lift_fst _ _ _

@[simp]
lemma fiberObjEquivHom_symm_naturality {X Y : FiniteEtale S} (f : X ⟶ Y) (x) :
    (fiber «ξ»).map f ((fiberObjEquivHom «ξ» X).symm x) =
      (fiberObjEquivHom «ξ» Y).symm (x ≫ f.hom) :=
  by
    let baseIso : (Over.mk «ξ»).left ≅ Spec (.of Ω) :=
      eqToIso (Over.mk_left «ξ»)
    let : IsFiniteEtale baseIso.hom := by constructor
    let T : FiniteEtale (Spec (.of Ω)) := FiniteEtale.mk baseIso.hom
    have baseIso_hom_comp : baseIso.hom ≫ «ξ» = (Over.mk «ξ»).hom := by
      change eqToHom (Over.mk_left «ξ») ≫ «ξ» = (Over.mk «ξ»).hom
      exact eq_of_heq (eqToHom_comp_heq «ξ» (Over.mk_left «ξ»))
    let t : T.left := by
      exact baseIso.inv.base
        (Classical.choice (inferInstance : Nonempty (Spec (.of Ω))))
    let sourceMap {Z : FiniteEtale S} (x : Over.mk «ξ» ⟶ Z.toComma) :
        T.left ⟶ Z.left := x.left
    let liftHom {Z : FiniteEtale S} (x : Over.mk «ξ» ⟶ Z.toComma) :
        T ⟶ (pullback «ξ»).obj Z :=
      MorphismProperty.Over.homMk
        (Limits.pullback.lift (sourceMap x) T.hom (by
          change x.left ≫ Z.toComma.hom = baseIso.hom ≫ «ξ»
          exact x.w.trans baseIso_hom_comp.symm))
        (Limits.pullback.lift_snd _ _ _)
    have liftHom_fst {Z : FiniteEtale S} (z : Over.mk «ξ» ⟶ Z.toComma) :
        (liftHom z).left ≫ Limits.pullback.fst Z.hom «ξ» = sourceMap z := by
      change Limits.pullback.lift (sourceMap z) T.hom _ ≫
        Limits.pullback.fst Z.hom «ξ» = sourceMap z
      exact Limits.pullback.lift_fst _ _ _
    have liftHom_snd {Z : FiniteEtale S} (z : Over.mk «ξ» ⟶ Z.toComma) :
        (liftHom z).left ≫ Limits.pullback.snd Z.hom «ξ» = T.hom := by
      change Limits.pullback.lift (sourceMap z) T.hom _ ≫
        Limits.pullback.snd Z.hom «ξ» = T.hom
      exact Limits.pullback.lift_snd _ _ _
    have pullbackMap_fst :
        ((pullback «ξ»).map f).left ≫ Limits.pullback.fst Y.hom «ξ» =
          Limits.pullback.fst X.hom «ξ» ≫ f.left := by
      change
        Limits.pullback.lift
            (Limits.pullback.fst X.hom «ξ» ≫ f.left)
            (Limits.pullback.snd X.hom «ξ») _ ≫
          Limits.pullback.fst Y.hom «ξ» =
        Limits.pullback.fst X.hom «ξ» ≫ f.left
      exact Limits.pullback.lift_fst _ _ _
    have pullbackMap_snd :
        ((pullback «ξ»).map f).left ≫ Limits.pullback.snd Y.hom «ξ» =
          Limits.pullback.snd X.hom «ξ» := by
      change
        Limits.pullback.lift
            (Limits.pullback.fst X.hom «ξ» ≫ f.left)
            (Limits.pullback.snd X.hom «ξ») _ ≫
          Limits.pullback.snd Y.hom «ξ» =
        Limits.pullback.snd X.hom «ξ»
      exact Limits.pullback.lift_snd _ _ _
    have h : liftHom x ≫ (pullback «ξ»).map f = liftHom (x ≫ f.hom) := by
      apply MorphismProperty.Over.Hom.ext
      apply Limits.pullback.hom_ext
      · change
          ((liftHom x).left ≫ ((pullback «ξ»).map f).left) ≫
              Limits.pullback.fst Y.hom «ξ» =
            (liftHom (x ≫ f.hom)).left ≫ Limits.pullback.fst Y.hom «ξ»
        have lhs :
            ((liftHom x).left ≫ ((pullback «ξ»).map f).left) ≫
                Limits.pullback.fst Y.hom «ξ» =
              sourceMap x ≫ f.left := by
          calc
            ((liftHom x).left ≫ ((pullback «ξ»).map f).left) ≫
                Limits.pullback.fst Y.hom «ξ» =
              (liftHom x).left ≫
                (((pullback «ξ»).map f).left ≫
                  Limits.pullback.fst Y.hom «ξ») := Category.assoc _ _ _
            _ = (liftHom x).left ≫
                  (Limits.pullback.fst X.hom «ξ» ≫ f.left) :=
                congrArg (fun q ↦ (liftHom x).left ≫ q) pullbackMap_fst
            _ = ((liftHom x).left ≫ Limits.pullback.fst X.hom «ξ») ≫ f.left :=
                (Category.assoc _ _ _).symm
            _ = sourceMap x ≫ f.left :=
                congrArg (fun q ↦ q ≫ f.left) (liftHom_fst x)
        have middle :
            sourceMap x ≫ f.left = sourceMap (x ≫ f.hom) := by
          rfl
        have rhs :
            (liftHom (x ≫ f.hom)).left ≫ Limits.pullback.fst Y.hom «ξ» =
              sourceMap (x ≫ f.hom) :=
          liftHom_fst _
        exact lhs.trans (middle.trans rhs.symm)
      · change
          ((liftHom x).left ≫ ((pullback «ξ»).map f).left) ≫
              Limits.pullback.snd Y.hom «ξ» =
            (liftHom (x ≫ f.hom)).left ≫ Limits.pullback.snd Y.hom «ξ»
        have lhs :
            ((liftHom x).left ≫ ((pullback «ξ»).map f).left) ≫
                Limits.pullback.snd Y.hom «ξ» = T.hom := by
          calc
            ((liftHom x).left ≫ ((pullback «ξ»).map f).left) ≫
                Limits.pullback.snd Y.hom «ξ» =
              (liftHom x).left ≫
                (((pullback «ξ»).map f).left ≫
                  Limits.pullback.snd Y.hom «ξ») := Category.assoc _ _ _
            _ = (liftHom x).left ≫ Limits.pullback.snd X.hom «ξ» :=
                congrArg (fun q ↦ (liftHom x).left ≫ q) pullbackMap_snd
            _ = T.hom := liftHom_snd x
        have rhs :
            (liftHom (x ≫ f.hom)).left ≫ Limits.pullback.snd Y.hom «ξ» =
              T.hom :=
          liftHom_snd _
        exact lhs.trans rhs.symm
    change ((forgetScheme Ω).map (liftHom x) ≫
        (forgetScheme Ω).map ((pullback «ξ»).map f)) t =
      (forgetScheme Ω).map (liftHom (x ≫ f.hom)) t
    rw [← Functor.map_comp, h]

@[reassoc]
lemma fiberObjEquivHom_naturality {X Y : FiniteEtale S} (f : X ⟶ Y) (x) :
    (fiberObjEquivHom «ξ» X x) ≫ f.hom = fiberObjEquivHom «ξ» Y ((fiber «ξ»).map f x) :=
  by
    apply (fiberObjEquivHom «ξ» Y).symm.injective
    simpa using
      (fiberObjEquivHom_symm_naturality «ξ» f (fiberObjEquivHom «ξ» X x)).symm

/-- The natural identification of the fiber functor with morphisms from the field point in the
over category. -/
noncomputable
def fiberIsoCoyoneda :
    fiber «ξ» ⋙ CategoryTheory.forget FintypeCat ≅ forget _ ⋙ coyoneda.obj ⟨Over.mk «ξ»⟩ :=
  NatIso.ofComponents (fun X ↦ (equivEquivIso (fiberObjEquivHom «ξ» X)))
    (fun {X Y} f ↦ by
      ext x
      exact (fiberObjEquivHom_naturality «ξ» f x).symm)

variable (k K Ω : Type u) [Field k] [Field K] [Algebra k K] [Field Ω] [Algebra k Ω]
  [Algebra K Ω] [IsScalarTower k K Ω]

variable (X : FiniteEtale (Spec (.of k)))

noncomputable
instance (X : FiniteEtale (Spec (.of k))) [IsSepClosed K] :
    MulAction (K ≃ₐ[k] K) ((fib k K).obj X) where
  smul g x :=
    (fiberIsoCoyoneda (ξ k K)).inv.app X
      (g • (fiberIsoCoyoneda (ξ k K)).hom.app X x)
  one_smul x := by
    change (fiberObjEquivHom (ξ k K) X).symm
      (1 • fiberObjEquivHom (ξ k K) X x) = x
    have hOne : (1 : K ≃ₐ[k] K) • fiberObjEquivHom (ξ k K) X x =
        fiberObjEquivHom (ξ k K) X x :=
      one_smul (K ≃ₐ[k] K) _
    exact (congrArg (fiberObjEquivHom (ξ k K) X).symm hOne).trans
      (Equiv.symm_apply_apply _ _)
  mul_smul g h x := by
    change (fiberObjEquivHom (ξ k K) X).symm
        ((g * h) • fiberObjEquivHom (ξ k K) X x) =
      (fiberObjEquivHom (ξ k K) X).symm
        (g • fiberObjEquivHom (ξ k K) X
          ((fiberObjEquivHom (ξ k K) X).symm
            (h • fiberObjEquivHom (ξ k K) X x)))
    rw [Equiv.apply_symm_apply, mul_smul]

lemma algEquiv_smul_fiber_def [IsSepClosed K] (g : K ≃ₐ[k] K) (x : (fib k K).obj X) :
    g • x = (fiberObjEquivHom (ξ k K) X).symm (g • ((fiberObjEquivHom (ξ k K) X) x)) :=
  rfl

lemma isField_of_isConnected (X : FiniteEtale (Spec (.of k))) [IsConnected X] :
    IsField Γ(X.left, ⊤) :=
  by
    let Omega := AlgebraicClosure k
    let xi : Spec (.of Omega) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom <| algebraMap k Omega)
    let F := fiber xi
    have hX : Nonempty X.left :=
      (nonempty_fiber_of_isConnected F X).map fun x ↦ fiberPt x
    obtain ⟨x⟩ := hX
    let hcomponents : Finite (ConnectedComponents X.left) := inferInstance
    let U := X.left.connectedComponents
    let i : ConnectedComponents X.left := ConnectedComponents.mk x
    let hUconn : ConnectedSpace (U.X i) := by
      dsimp only [U]
      infer_instance
    let hXet : IsFiniteEtale X.hom := X.2
    let hcomp : IsFiniteEtale (U.f i ≫ X.hom) := by
      have : IsOpenImmersion (U.f i) := by
        dsimp only [U, Scheme.connectedComponents]
        infer_instance
      have hComponent : IsFiniteEtale (U.f i) :=
        @IsFiniteEtale.mk _ _ _ inferInstance inferInstance
      let : IsFiniteEtale (U.f i) := hComponent
      infer_instance
    let Y : FiniteEtale (Spec (.of k)) :=
      @FiniteEtale.mk _ _ (U.f i ≫ X.hom) hcomp
    let j : Y ⟶ X :=
      MorphismProperty.Over.homMk (by
        simpa only [Y, FiniteEtale.mk_left] using U.f i)
    let : Mono j := by
      apply (FiniteEtale.forget _ ⋙ Over.forget _).mono_of_mono_map
      change Mono (U.f i)
      infer_instance
    have : Nonempty Y.left := by
      have hYi : Nonempty (U.X i) := by
        refine ⟨⟨x, ?_⟩⟩
        change ConnectedComponents.mk x ∈ ({i} : Set (ConnectedComponents X.left))
        exact Set.mem_singleton_iff.mpr rfl
      simpa only [Y, FiniteEtale.mk_left] using hYi
    let : Subsingleton (Spec (.of k)) := inferInstance
    have hFY : Nonempty (F.obj Y) := by
      change Nonempty ((pullback xi).obj Y).left
      obtain ⟨ω⟩ := (inferInstance : Nonempty (Spec (.of Omega)))
      let : PreconnectedSpace
          ((Functor.fromPUnit (Spec (.of k))).obj Y.right) := by
        change PreconnectedSpace (Spec (.of k))
        infer_instance
      let : Nonempty ((𝟭 Scheme).obj Y.left) := by
        change Nonempty Y.left
        infer_instance
      let : Surjective Y.hom := IsFiniteEtale.surjective Y.hom
      obtain ⟨y, hy⟩ := Y.hom.surjective (xi.base ω)
      obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback y ω hy
      exact ⟨z⟩
    let : IsIso j :=
      let : Nonempty ((𝟭 Scheme).obj Y.left) := by
        change Nonempty Y.left
        infer_instance
      IsConnected.noTrivialComponent Y j
        ((not_initial_iff_fiber_nonempty F Y).mpr hFY)
    let hjhom : IsIso j.hom := (FiniteEtale.forget _).map_isIso j
    let hjleft : IsIso j.left :=
      @Functor.map_isIso _ _ _ _ _ _
        (_root_.CategoryTheory.Over.forget _) j.hom hjhom
    let eY : Y.left ≅ U.X i :=
      eqToIso (by simp only [Y, FiniteEtale.mk_left])
    let hYconn : ConnectedSpace Y.left :=
      eY.hom.homeomorph.connectedSpace_iff.mpr hUconn
    have hconn : ConnectedSpace X.left :=
      (@asIso _ _ _ _ j.left hjleft).hom.homeomorph.connectedSpace_iff.mp hYconn
    let : ConnectedSpace (Spec Γ(X.left, ⊤)) := by
      rw [← X.left.isoSpec.hom.homeomorph.connectedSpace_iff]
      exact hconn
    let : _root_.IsReduced Γ(X.left, ⊤) :=
      Algebra.FormallyUnramified.isReduced_of_field k Γ(X.left, ⊤)
    let : IsArtinianRing Γ(X.left, ⊤) :=
      IsArtinianRing.of_finite k Γ(X.left, ⊤)
    let : PreconnectedSpace (PrimeSpectrum Γ(X.left, ⊤)) := by
      change PreconnectedSpace (Spec Γ(X.left, ⊤))
      infer_instance
    let : Nontrivial Γ(X.left, ⊤) :=
      PrimeSpectrum.nontrivial
        (Classical.choice (inferInstance : Nonempty (Spec Γ(X.left, ⊤))))
    rw [← PrimeSpectrum.subsingleton_iff_isField_of_isReduced]
    constructor
    intro p q
    exact PreconnectedSpace.constant (f := id)
      (inferInstance : PreconnectedSpace (PrimeSpectrum Γ(X.left, ⊤))) continuous_id

noncomputable instance (X : FiniteEtale (Spec (.of k))) [IsConnected X] : Field Γ(X.left, ⊤) :=
  (isField_of_isConnected _ X).toField


instance : ContinuousSMul (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) := by
  let : DiscreteTopology (Over.mk (ξ k K) ⟶ X.toComma) :=
    discreteTopology_bot _
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  let φ : Γ(X.left, ⊤) →ₐ[k] K := homEquivAlgHom k K X x
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := Γ(X.left, ⊤))
  let openStabilizer (a : Γ(X.left, ⊤)) : OpenSubgroup (K ≃ₐ[k] K) :=
    ⟨MulAction.stabilizer (K ≃ₐ[k] K) (φ a), by
      let E := IntermediateField.adjoin k {φ a}
      let : FiniteDimensional k E :=
        IntermediateField.adjoin.finiteDimensional
          ((Algebra.IsIntegral.isIntegral a).map φ)
      convert! IntermediateField.fixingSubgroup_isOpen E
      ext g
      simpa using
        (IntermediateField.forall_mem_adjoin_smul_eq_self_iff
          k (S := {φ a}) g).symm⟩
  let H : OpenSubgroup (K ≃ₐ[k] K) := s.inf openStabilizer
  apply Subgroup.isOpen_mono (H₁ := H.toSubgroup) ?_ H.isOpen
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  apply (homEquivAlgHom k K X).injective
  rw [homEquivAlgHom_smul]
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro a ha
  change g • φ a = φ a
  exact MulAction.mem_stabilizer_iff.mp
    ((show H ≤ openStabilizer a from Finset.inf_le ha) hg)

instance isGalois_of_isGalois (X : FiniteEtale (Spec (.of k))) [IsGalois X] :
    IsGalois k Γ(X.left, ⊤) :=
  by
    let A := Γ(X.left, ⊤)
    change IsGalois k A
    let Omega := AlgebraicClosure k
    let xi : Spec (.of Omega) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom <| algebraMap k Omega)
    let F := fiber xi
    let a : F.obj X := Classical.choice inferInstance
    let e : F.obj X ≃ (A →ₐ[k] Omega) :=
      (fiberObjEquivHom xi X).trans (homEquivAlgHom k Omega X)
    let : Algebra.IsSeparable k A :=
      Algebra.FormallyUnramified.isSeparable k A
    have hAut : Nat.card (Aut X) = Module.finrank k A := calc
      Nat.card (Aut X) = Nat.card (F.obj X) :=
        Nat.card_congr (evaluationEquivOfIsGalois F X a)
      _ = Nat.card (A →ₐ[k] Omega) := Nat.card_congr e
      _ = Module.finrank k A :=
        AlgHom.natCard_of_splits k A Omega (fun _ ↦ IsAlgClosed.splits _)
    let toAlgHom (f : X ⟶ X) : A →ₐ[k] A :=
      { __ := f.left.appTop.hom,
        commutes' := fun z ↦ appTop_left_algebraMap k f z }
    let autToAlgEquiv : Aut X → (A ≃ₐ[k] A) := fun σ ↦
      AlgEquiv.ofAlgHom (toAlgHom σ.hom) (toAlgHom σ.inv) (by
        let e : X.left ≅ X.left := (forget _ ⋙ Over.forget _).mapIso σ
        apply AlgHom.coe_ringHom_injective
        change e.hom.appTop.hom.comp e.inv.appTop.hom =
          RingHom.id Γ(X.left, ⊤)
        rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, e.hom_inv_id]
        rw [Scheme.Hom.id_appTop]
        rfl) (by
        let e : X.left ≅ X.left := (forget _ ⋙ Over.forget _).mapIso σ
        apply AlgHom.coe_ringHom_injective
        change e.inv.appTop.hom.comp e.hom.appTop.hom =
          RingHom.id Γ(X.left, ⊤)
        rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
        rw [Scheme.Hom.id_appTop]
        rfl)
    have haut_injective : Function.Injective autToAlgEquiv := by
      intro σ τ h
      apply Aut.ext
      apply MorphismProperty.Over.Hom.ext
      apply Scheme.Hom.appTop_bijective_of_isAffine.injective
      ext z
      simpa [autToAlgEquiv, toAlgHom] using
        congrFun (congrArg (fun e : A ≃ₐ[k] A ↦ (e : A → A)) h) z
    have hle : Nat.card (A ≃ₐ[k] A) ≤ Module.finrank k A := calc
      Nat.card (A ≃ₐ[k] A) = Nat.card (A →ₐ[k] A) :=
        Nat.card_congr (algEquivEquivAlgHom k A)
      _ ≤ Module.finrank k A := card_algHom_le_finrank k A A
    have hge : Module.finrank k A ≤ Nat.card (A ≃ₐ[k] A) := by
      rw [← hAut]
      exact Nat.card_le_card_of_injective autToAlgEquiv haut_injective
    exact IsGalois.of_card_aut_eq_finrank k A (le_antisymm hle hge)

instance [IsGalois k K] (X : FiniteEtale (Spec (.of k))) [IsGalois X] :
    MulAction.IsPretransitive (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) := by
  constructor
  intro x y
  let : Algebra Γ(X.left, ⊤) K := (homEquivAlgHom k K X x).toAlgebra
  obtain ⟨g, h⟩ := MulAction.exists_smul_eq (K ≃ₐ[k] K)
    (homEquivAlgHom k K X x) (homEquivAlgHom k K X y)
  use g
  apply (homEquivAlgHom k K X).injective
  rwa [homEquivAlgHom_smul]


attribute [local instance] IsSepClosure.sep_closed

variable [IsSepClosure k K]

instance : IsFundamentalGroup (fib k K) (K ≃ₐ[k] K) where
  naturality g X Y f x := by
    apply (fiberObjEquivHom (ξ k K) Y).injective
    rw [algEquiv_smul_fiber_def, algEquiv_smul_fiber_def]
    simp only [fiberObjEquivHom_symm_naturality, Equiv.apply_symm_apply]
    rw [← fiberObjEquivHom_naturality (ξ k K) f x]
    ext1
    simp only [algEquiv_smul_hom]
    exact Category.assoc _ _ _
  continuous_smul X := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    let e := fiberObjEquivHom (ξ k K) X
    let : DiscreteTopology (Over.mk (ξ k K) ⟶ X.toComma) :=
      discreteTopology_bot _
    have hopen := stabilizer_isOpen (K ≃ₐ[k] K) (e x)
    convert hopen using 1
    ext g
    change (g • x = x) ↔ (g • e x = e x)
    rw [algEquiv_smul_fiber_def]
    constructor
    · intro h
      simpa only [e, Equiv.apply_symm_apply] using congrArg e h
    · intro h
      apply e.injective
      simpa only [e, Equiv.apply_symm_apply] using h
  transitive_of_isGalois X _ := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (K ≃ₐ[k] K)
      (fiberObjEquivHom _ _ x) (fiberObjEquivHom _ _ y)
    use g
    rw [algEquiv_smul_fiber_def]
    apply (fiberObjEquivHom (ξ k K) X).injective
    simp [hg]
  non_trivial' g H := by
    refine eq_one_of_smul_eq (k := k) (K := K) g ?_
    intro X x
    apply (fiberObjEquivHom (ξ k K) X).symm.injective
    specialize H X ((fiberObjEquivHom (ξ k K) X).symm x)
    rwa [algEquiv_smul_fiber_def, Equiv.apply_symm_apply] at H

end FiniteEtale

end AlgebraicGeometry
