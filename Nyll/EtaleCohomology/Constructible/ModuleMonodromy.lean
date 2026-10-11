/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantEquivalence
import Nyll.EtaleCohomology.Constructible.LocallyConstant
import Nyll.EtaleCohomology.Constructible.Monodromy
import Nyll.EtaleCohomology.Constructible.ModuleUnderlying
import Nyll.EtaleCohomology.Constructible.LocallyConstantProducts
import Nyll.EtaleCohomology.Sites.ModuleSetComparison
import Nyll.EtaleFundamentalGroups.FiniteEtale.GaloisCategory
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Topology.Category.FinTopCat
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Order

/-!
# Linear monodromy on actual geometric stalks

Over a finite commutative coefficient ring, finite type locally constant
étale module sheaves carry a continuous linear action of the étale fundamental
group on their actual geometric stalks. The underlying set action is naturally
isomorphic to the finite continuous monodromy action of the underlying set sheaf.

Linearity is proved from naturality: the square of the sheaf is locally constant,
the stalk preserves its product, and monodromy commutes with the projections,
their sum, and scalar endomorphisms. Additivity and scalar compatibility of the
stalk functor itself are checked using the canonical maps into its defining
filtered colimit. No finite field assumption on the base is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped FintypeCatDiscrete
universe u
namespace EtaleCohomology

/-- The full category of finite type locally constant étale module sheaves. -/
abbrev EtaleFiniteTypeLocallyConstantModuleSheaf (X : Scheme.{u})
    (R : Type u) [CommRing R] : Type (u + 1) :=
  ObjectProperty.FullSubcategory (IsEtaleFiniteTypeLocallyConstant (X := X) R)

variable {X : Scheme.{u}} {R : Type u} [CommRing R] [Finite R]

/-- Forgetting a finite-ring local system gives a finite locally constant set sheaf. -/
def finiteLocallyConstantModuleUnderlying :
    EtaleFiniteTypeLocallyConstantModuleSheaf X R ⥤ EtaleFiniteLocallyConstantSetSheaf X :=
  ObjectProperty.lift _
    (ObjectProperty.ι (IsEtaleFiniteTypeLocallyConstant (X := X) R) ⋙
      etaleModuleUnderlying X R)
    (fun G => G.property.isEtaleFiniteLocallyConstantSet)

variable [ConnectedSpace X] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ X)

/-- The finite continuous set action underlying a finite-ring local system. -/
abbrev finiteLocallyConstantModuleSetMonodromy :
    EtaleFiniteTypeLocallyConstantModuleSheaf X R ⥤
      ContAction FintypeCat.{u} (Aut (FiniteEtale.fiber ξ)) :=
  finiteLocallyConstantModuleUnderlying (X := X) (R := R) ⋙
    (finiteLocallyConstantSetMonodromy ξ).functor

/-- The set-theoretic monodromy carrier is naturally the actual module stalk. -/
def finiteLocallyConstantModuleStalkIso :
    finiteLocallyConstantModuleSetMonodromy (R := R) ξ ⋙
      forget₂ (ContAction FintypeCat.{u} (Aut (FiniteEtale.fiber ξ))) FintypeCat ⋙
      forget FintypeCat ≅
    ObjectProperty.ι (IsEtaleFiniteTypeLocallyConstant (X := X) R) ⋙
      (Scheme.pointSmallEtale ξ).sheafFiber (A := ModuleCat R) ⋙ forget (ModuleCat R) := by
  let L := finiteLocallyConstantModuleUnderlying (X := X) (R := R)
  let ι := ObjectProperty.ι (IsEtaleFiniteTypeLocallyConstant (X := X) R)
  let Φ := Scheme.pointSmallEtale ξ
  exact Functor.associator L _ _ ≪≫
    Functor.isoWhiskerLeft L (finiteLocallyConstantSetMonodromyStalkIso ξ) ≪≫
    (Functor.associator L _ _).symm ≪≫
    Functor.associator ι (etaleModuleUnderlying X R) (Φ.sheafFiber (A := Type u)) ≪≫
    Functor.isoWhiskerLeft ι (Φ.sheafFiberCompIso (forget (ModuleCat R)))

/-- Transport the finite set action onto the underlying set of the actual module stalk. -/
abbrev moduleStalkSetAction (G : EtaleFiniteTypeLocallyConstantModuleSheaf X R) :
    Action (Type u) (Aut (FiniteEtale.fiber ξ)) where
  V := ↥((Scheme.pointSmallEtale ξ).sheafFiber (A := ModuleCat R) |>.obj G.obj)
  ρ := ((finiteLocallyConstantModuleStalkIso ξ).app G).conj.toMonoidHom.comp
    ((Functor.mapEnd (((finiteLocallyConstantModuleSetMonodromy ξ).obj G).obj.V)
      (forget FintypeCat)).comp
      (((finiteLocallyConstantModuleSetMonodromy ξ).obj G).obj.ρ))

/-- The transported set action agrees with the finite continuous set action. -/
def moduleStalkSetActionIso (G : EtaleFiniteTypeLocallyConstantModuleSheaf X R) :
    ((forget FintypeCat).mapAction (Aut (FiniteEtale.fiber ξ))).obj
      ((finiteLocallyConstantModuleSetMonodromy ξ).obj G).obj ≅ moduleStalkSetAction ξ G :=
  Action.mkIso ((finiteLocallyConstantModuleStalkIso ξ).app G) (fun a => by
    change _ ≫ ((finiteLocallyConstantModuleStalkIso ξ).app G).hom =
      ((finiteLocallyConstantModuleStalkIso ξ).app G).hom ≫
        (((finiteLocallyConstantModuleStalkIso ξ).app G).inv ≫ _ ≫
          ((finiteLocallyConstantModuleStalkIso ξ).app G).hom)
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rfl)

private def moduleStalkSetActionMap {G H : EtaleFiniteTypeLocallyConstantModuleSheaf X R}
    (f : G ⟶ H) : moduleStalkSetAction ξ G ⟶ moduleStalkSetAction ξ H :=
  (moduleStalkSetActionIso ξ G).inv ≫
    ((forget FintypeCat).mapAction (Aut (FiniteEtale.fiber ξ))).map
      (((finiteLocallyConstantModuleSetMonodromy ξ).map f).hom) ≫ (moduleStalkSetActionIso ξ H).hom

private lemma moduleStalkSetActionMap_hom {G H : EtaleFiniteTypeLocallyConstantModuleSheaf X R}
    (f : G ⟶ H) : (moduleStalkSetActionMap ξ f).hom =
      (forget (ModuleCat R)).map ((Scheme.pointSmallEtale ξ).sheafFiber.map f.hom) := by
  let e := finiteLocallyConstantModuleStalkIso (R := R) ξ
  have h : (moduleStalkSetActionMap ξ f).hom =
      (e.app G).inv ≫ ((e.app G).hom ≫
        (forget (ModuleCat R)).map ((Scheme.pointSmallEtale ξ).sheafFiber.map f.hom)) :=
    congrArg ((e.app G).inv ≫ ·) (e.hom.naturality f)
  exact h.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (forget (ModuleCat R)).map
      ((Scheme.pointSmallEtale ξ).sheafFiber.map f.hom)) (e.app G).inv_hom_id).trans
        (Category.id_comp _)))

/-- Every actual stalk map of module sheaves is equivariant. -/
theorem moduleStalkSetAction_naturality
    {G H : EtaleFiniteTypeLocallyConstantModuleSheaf X R} (f : G ⟶ H)
    (γ : Aut (FiniteEtale.fiber ξ))
    (x : (Scheme.pointSmallEtale ξ).sheafFiber (A := ModuleCat R) |>.obj G.obj) :
    (Scheme.pointSmallEtale ξ).sheafFiber.map f.hom ((moduleStalkSetAction ξ G).ρ γ x) =
      (moduleStalkSetAction ξ H).ρ γ ((Scheme.pointSmallEtale ξ).sheafFiber.map f.hom x) := by
  have h := (moduleStalkSetActionMap ξ f).comm γ
  rw [moduleStalkSetActionMap_hom] at h
  exact congrArg (fun k : (moduleStalkSetAction ξ G).V ⟶
    (moduleStalkSetAction ξ H).V => k x) h

omit [Finite R] [ConnectedSpace X] in
private lemma moduleStalk_map_add
    {G H : Sheaf X.smallEtaleTopology (ModuleCat R)} (f g : G ⟶ H) :
    (Scheme.pointSmallEtale ξ).sheafFiber.map (f + g) =
      (Scheme.pointSmallEtale ξ).sheafFiber.map f +
        (Scheme.pointSmallEtale ξ).sheafFiber.map g := by
  apply (Scheme.pointSmallEtale ξ).presheafFiber_hom_ext
  intro U x
  change (Scheme.pointSmallEtale ξ).toPresheafFiber U x G.obj ≫
      (Scheme.pointSmallEtale ξ).presheafFiber.map (f.hom + g.hom) =
    (Scheme.pointSmallEtale ξ).toPresheafFiber U x G.obj ≫
      ((Scheme.pointSmallEtale ξ).presheafFiber.map f.hom +
        (Scheme.pointSmallEtale ξ).presheafFiber.map g.hom)
  simp only [GrothendieckTopology.Point.toPresheafFiber_naturality,
    Preadditive.comp_add, Preadditive.add_comp, NatTrans.app_add]

omit [Finite R] [ConnectedSpace X] in
private lemma moduleStalk_map_smul
    {G H : Sheaf X.smallEtaleTopology (ModuleCat R)} (r : R) (f : G ⟶ H) :
    (Scheme.pointSmallEtale ξ).sheafFiber.map (r • f) =
      r • (Scheme.pointSmallEtale ξ).sheafFiber.map f := by
  apply (Scheme.pointSmallEtale ξ).presheafFiber_hom_ext
  intro U x
  change (Scheme.pointSmallEtale ξ).toPresheafFiber U x G.obj ≫
      (Scheme.pointSmallEtale ξ).presheafFiber.map (r • f.hom) =
    (Scheme.pointSmallEtale ξ).toPresheafFiber U x G.obj ≫
      (r • (Scheme.pointSmallEtale ξ).presheafFiber.map f.hom)
  simp only [GrothendieckTopology.Point.toPresheafFiber_naturality,
    Linear.comp_smul, Linear.smul_comp, NatTrans.app_smul]

/-- Naturality for the two projections and their sum gives additivity of monodromy. -/
theorem moduleStalkSetAction_map_add (G : EtaleFiniteTypeLocallyConstantModuleSheaf X R)
    (γ : Aut (FiniteEtale.fiber ξ))
    (x y : (Scheme.pointSmallEtale ξ).sheafFiber (A := ModuleCat R) |>.obj G.obj) :
    (moduleStalkSetAction ξ G).ρ γ (x + y) =
      (moduleStalkSetAction ξ G).ρ γ x + (moduleStalkSetAction ξ G).ρ γ y := by
  let P : EtaleFiniteTypeLocallyConstantModuleSheaf X R :=
    ⟨G.obj ⨯ G.obj, G.property.selfProd⟩
  let Φ := (Scheme.pointSmallEtale ξ).sheafFiber (A := ModuleCat R)
  let K := Φ ⋙ forget (ModuleCat R)
  let e : K.obj (G.obj ⨯ G.obj) ≅ K.obj G.obj × K.obj G.obj :=
    PreservesLimitPair.iso K G.obj G.obj ≪≫ Types.binaryProductIso _ _
  let z : Φ.obj P.obj := e.inv (x, y)
  have hx : Φ.map (prod.fst : P.obj ⟶ G.obj) z = x := by
    have h : e.inv ≫ K.map prod.fst = ↾(_root_.Prod.fst) := by
      dsimp only [e, Iso.trans_inv]
      rw [Category.assoc, PreservesLimitPair.iso_inv_fst,
        Types.binaryProductIso_inv_comp_fst]
    exact congrArg (fun k : K.obj G.obj × K.obj G.obj ⟶ K.obj G.obj => k (x, y)) h
  have hy : Φ.map (prod.snd : P.obj ⟶ G.obj) z = y := by
    have h : e.inv ≫ K.map prod.snd = ↾(_root_.Prod.snd) := by
      dsimp only [e, Iso.trans_inv]
      rw [Category.assoc, PreservesLimitPair.iso_inv_snd,
        Types.binaryProductIso_inv_comp_snd]
    exact congrArg (fun k : K.obj G.obj × K.obj G.obj ⟶ K.obj G.obj => k (x, y)) h
  have hf := moduleStalkSetAction_naturality ξ
    (ObjectProperty.homMk prod.fst : P ⟶ G) γ z
  have hs := moduleStalkSetAction_naturality ξ
    (ObjectProperty.homMk prod.snd : P ⟶ G) γ z
  have ha := moduleStalkSetAction_naturality ξ
    (ObjectProperty.homMk (prod.fst + prod.snd) : P ⟶ G) γ z
  change Φ.map (prod.fst + prod.snd) ((moduleStalkSetAction ξ P).ρ γ z) =
    (moduleStalkSetAction ξ G).ρ γ (Φ.map (prod.fst + prod.snd) z) at ha
  rw [moduleStalk_map_add ξ] at ha
  change Φ.map prod.fst ((moduleStalkSetAction ξ P).ρ γ z) +
      Φ.map prod.snd ((moduleStalkSetAction ξ P).ρ γ z) =
    (moduleStalkSetAction ξ G).ρ γ (Φ.map prod.fst z + Φ.map prod.snd z) at ha
  have hf' : Φ.map prod.fst ((moduleStalkSetAction ξ P).ρ γ z) =
      (moduleStalkSetAction ξ G).ρ γ x := hf.trans (congrArg _ hx)
  have hs' : Φ.map prod.snd ((moduleStalkSetAction ξ P).ρ γ z) =
      (moduleStalkSetAction ξ G).ρ γ y := hs.trans (congrArg _ hy)
  exact (congrArg ((moduleStalkSetAction ξ G).ρ γ)
    (congrArg₂ (· + ·) hx hy)).symm.trans
      (ha.symm.trans (congrArg₂ (· + ·) hf' hs'))

/-- Naturality for scalar endomorphisms gives compatibility with the coefficient ring. -/
theorem moduleStalkSetAction_map_smul (G : EtaleFiniteTypeLocallyConstantModuleSheaf X R)
    (γ : Aut (FiniteEtale.fiber ξ)) (r : R)
    (x : (Scheme.pointSmallEtale ξ).sheafFiber (A := ModuleCat R) |>.obj G.obj) :
    (moduleStalkSetAction ξ G).ρ γ (r • x) = r • (moduleStalkSetAction ξ G).ρ γ x := by
  have h := moduleStalkSetAction_naturality ξ
    (ObjectProperty.homMk (r • 𝟙 G.obj) : G ⟶ G) γ x
  change (Scheme.pointSmallEtale ξ).sheafFiber.map (r • 𝟙 G.obj)
      ((moduleStalkSetAction ξ G).ρ γ x) =
    (moduleStalkSetAction ξ G).ρ γ ((Scheme.pointSmallEtale ξ).sheafFiber.map (r • 𝟙 G.obj) x) at h
  rw [moduleStalk_map_smul ξ, CategoryTheory.Functor.map_id] at h
  exact h.symm

/-- Linear monodromy on the actual geometric stalk, with its original module structure. -/
abbrev moduleStalkMonodromy (G : EtaleFiniteTypeLocallyConstantModuleSheaf X R) :
    Action (ModuleCat R) (Aut (FiniteEtale.fiber ξ)) where
  V := (Scheme.pointSmallEtale ξ).sheafFiber.obj G.obj
  ρ :=
    { toFun := fun γ => ModuleCat.ofHom
        { toFun := (moduleStalkSetAction ξ G).ρ γ
          map_add' := moduleStalkSetAction_map_add ξ G γ
          map_smul' := moduleStalkSetAction_map_smul ξ G γ }
      map_one' := by
        apply (forget (ModuleCat R)).map_injective
        exact (moduleStalkSetAction ξ G).ρ.map_one
      map_mul' := fun γ δ => by
        apply (forget (ModuleCat R)).map_injective
        exact (moduleStalkSetAction ξ G).ρ.map_mul γ δ }

/-- Taking the geometric stalk as a linear representation is functorial. -/
def finiteLocallyConstantModuleMonodromy :
    EtaleFiniteTypeLocallyConstantModuleSheaf X R ⥤
      Action (ModuleCat R) (Aut (FiniteEtale.fiber ξ)) where
  obj := moduleStalkMonodromy ξ
  map f :=
    { hom := (Scheme.pointSmallEtale ξ).sheafFiber.map f.hom
      comm := fun γ => by
        ext x
        exact moduleStalkSetAction_naturality ξ f γ x }
  map_id G := Action.Hom.ext ((Scheme.pointSmallEtale ξ).sheafFiber.map_id G.obj)
  map_comp f g := Action.Hom.ext ((Scheme.pointSmallEtale ξ).sheafFiber.map_comp f.hom g.hom)

/-- Forgetting the linear structure recovers finite-set monodromy, naturally. -/
def finiteLocallyConstantModuleMonodromyUnderlyingIso :
    finiteLocallyConstantModuleSetMonodromy (R := R) ξ ⋙
      ObjectProperty.ι (Action.isContinuous FintypeCat.{u} (Aut (FiniteEtale.fiber ξ))) ⋙
      (forget FintypeCat).mapAction (Aut (FiniteEtale.fiber ξ)) ≅
    finiteLocallyConstantModuleMonodromy (R := R) ξ ⋙
      (forget (ModuleCat R)).mapAction (Aut (FiniteEtale.fiber ξ)) :=
  NatIso.ofComponents (moduleStalkSetActionIso ξ) (fun f =>
    Action.Hom.ext ((finiteLocallyConstantModuleStalkIso ξ).hom.naturality f))

/-- The actual geometric stalk of a finite-ring local system is a finite module. -/
theorem finite_moduleStalk (G : EtaleFiniteTypeLocallyConstantModuleSheaf X R) :
    Finite ((Scheme.pointSmallEtale ξ).sheafFiber (A := ModuleCat R) |>.obj G.obj) :=
  Finite.of_surjective (α := ((finiteLocallyConstantModuleSetMonodromy ξ).obj G).obj.V)
    ((finiteLocallyConstantModuleStalkIso ξ).app G).hom
    (ConcreteCategory.bijective_of_isIso ((finiteLocallyConstantModuleStalkIso ξ).app G).hom).2

/-- The linear action is continuous when the finite geometric stalk is discrete. -/
theorem moduleStalkMonodromy_continuous
    (G : EtaleFiniteTypeLocallyConstantModuleSheaf X R) :
    letI : TopologicalSpace ((Scheme.pointSmallEtale ξ).sheafFiber
      (A := ModuleCat R) |>.obj G.obj) := ⊥
    Continuous (fun p : Aut (FiniteEtale.fiber ξ) ×
        ((Scheme.pointSmallEtale ξ).sheafFiber (A := ModuleCat R) |>.obj G.obj) =>
      ((moduleStalkMonodromy ξ G).ρ p.1).hom p.2) := by
  let : TopologicalSpace ((Scheme.pointSmallEtale ξ).sheafFiber
    (A := ModuleCat R) |>.obj G.obj) := ⊥
  have : DiscreteTopology ((Scheme.pointSmallEtale ξ).sheafFiber
    (A := ModuleCat R) |>.obj G.obj) := ⟨rfl⟩
  let A := (finiteLocallyConstantModuleSetMonodromy ξ).obj G
  let e : ↥A.obj.V ≅ ↥((Scheme.pointSmallEtale ξ).sheafFiber
      (A := ModuleCat R) |>.obj G.obj) := (finiteLocallyConstantModuleStalkIso ξ).app G
  have hA : Continuous (fun p : Aut (FiniteEtale.fiber ξ) × A.obj.V =>
      ((forget FintypeCat).map (A.obj.ρ p.1)) p.2) := A.property.continuous_smul
  have hi : Continuous (fun p : Aut (FiniteEtale.fiber ξ) ×
      ((Scheme.pointSmallEtale ξ).sheafFiber (A := ModuleCat R) |>.obj G.obj) =>
      (p.1, e.inv p.2)) :=
    continuous_fst.prodMk (continuous_of_discreteTopology.comp continuous_snd)
  have he : Continuous (fun x : A.obj.V => e.hom x) := continuous_of_discreteTopology
  exact he.comp (hA.comp hi)

end EtaleCohomology
