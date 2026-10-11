/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.ContinuousActions.FiniteLimitsAndColimits
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion

/-!
# Uniqueness of the fiber functor on finite continuous actions

This file proves Stacks Project, Tag `0BMV`.
-/

universe u

noncomputable section

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.FiniteContinuousAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private abbrev OpenKernel :=
  LocalClassFieldTheory.OpenFiniteIndexNormalSubgroup G

private instance : Min (OpenKernel G) where
  min H K :=
    ⟨H.1 ⊓ K.1, by
      let : H.toOpenNormalSubgroup.toSubgroup.FiniteIndex := H.finiteIndex'
      let : K.toOpenNormalSubgroup.toSubgroup.FiniteIndex := K.finiteIndex'
      change Subgroup.FiniteIndex
        (H.toOpenNormalSubgroup.toSubgroup ⊓ K.toOpenNormalSubgroup.toSubgroup)
      infer_instance⟩

private instance : SemilatticeInf (OpenKernel G) :=
  Subtype.semilatticeInf fun H K hH hK => by
    let : H.toSubgroup.FiniteIndex := hH
    let : K.toSubgroup.FiniteIndex := hK
    change Subgroup.FiniteIndex (H.toSubgroup ⊓ K.toSubgroup)
    infer_instance

private def topOpenKernel : OpenKernel G where
  val :=
    { toOpenSubgroup :=
        { toSubgroup := ⊤
          isOpen' := isOpen_univ }
      isNormal' := by infer_instance }
  property := by infer_instance

private instance : Nonempty (OpenKernel G) :=
  ⟨topOpenKernel G⟩

private noncomputable instance quotientFintype (H : OpenKernel G) :
    Fintype (G ⧸ H.toOpenNormalSubgroup.toSubgroup) :=
  Subgroup.fintypeQuotientOfFiniteIndex

private noncomputable instance quotientFinite (H : OpenKernel G) :
    Finite (G ⧸ H.toOpenNormalSubgroup.toSubgroup) := by
  let : Fintype (G ⧸ H.toOpenNormalSubgroup.toSubgroup) :=
    quotientFintype G H
  infer_instance

private theorem quotient_continuousSMul
    (K : Subgroup G) [K.Normal]
    [TopologicalSpace (G ⧸ K)] [DiscreteTopology (G ⧸ K)]
    (hK : IsOpen (K : Set G)) :
    ContinuousSMul G (G ⧸ K) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K q
  convert hK using 1
  ext g
  change g • (QuotientGroup.mk a : G ⧸ K) =
      QuotientGroup.mk a ↔ g ∈ K
  constructor
  · intro hg
    change (QuotientGroup.mk g : G ⧸ K) * QuotientGroup.mk a =
      QuotientGroup.mk a at hg
    have hq : (QuotientGroup.mk g : G ⧸ K) = 1 := by
      exact mul_right_cancel (by simpa only [one_mul] using hg)
    exact (QuotientGroup.eq_one_iff g).mp hq
  · intro hg
    have hq : (QuotientGroup.mk g : G ⧸ K) = 1 :=
      (QuotientGroup.eq_one_iff g).mpr hg
    change (QuotientGroup.mk g : G ⧸ K) * QuotientGroup.mk a =
      QuotientGroup.mk a
    rw [hq, one_mul]

private noncomputable def quotientObject (H : OpenKernel G) :
    ContAction FintypeCat.{u} G := by
  let K := H.toOpenNormalSubgroup.toSubgroup
  letI : K.Normal := H.toOpenNormalSubgroup.isNormal'
  letI : K.FiniteIndex := H.finiteIndex'
  letI : TopologicalSpace (G ⧸ K) := ⊥
  letI : DiscreteTopology (G ⧸ K) := ⟨rfl⟩
  exact
    ⟨Action.FintypeCat.ofMulAction G (FintypeCat.of (G ⧸ K)),
      quotient_continuousSMul G K H.toOpenNormalSubgroup.isOpen'⟩

private noncomputable def quotientMap {H K : OpenKernel G} (f : H ⟶ K) :
    quotientObject G H ⟶ quotientObject G K := by
  let H' := H.toOpenNormalSubgroup.toSubgroup
  let K' := K.toOpenNormalSubgroup.toSubgroup
  letI : H'.FiniteIndex := H.finiteIndex'
  letI : K'.FiniteIndex := K.finiteIndex'
  letI : Fintype (G ⧸ H') := Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (G ⧸ K') := Subgroup.fintypeQuotientOfFiniteIndex
  exact ObjectProperty.homMk <|
    Action.FintypeCat.quotientToQuotientOfLE K' H'
      (LocalClassFieldTheory.OpenFiniteIndexNormalSubgroup.le_of_hom f)

private noncomputable def quotientDiagram :
    OpenKernel G ⥤ ContAction FintypeCat.{u} G where
  obj := quotientObject G
  map := quotientMap G
  map_id H := by
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    ext q
    obtain ⟨g, rfl⟩ :=
      QuotientGroup.mk'_surjective H.toOpenNormalSubgroup.toSubgroup q
    rfl
  map_comp {H K L} f g := by
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    ext q
    obtain ⟨a, rfl⟩ :=
      QuotientGroup.mk'_surjective H.toOpenNormalSubgroup.toSubgroup q
    rfl

private abbrev quotientFibers
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u}) :
    OpenKernel G ⥤ Type u :=
  quotientDiagram G ⋙ F ⋙ FintypeCat.incl

omit [IsTopologicalGroup G] in
private theorem nonempty_image_of_nonempty
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteColimits F] [PreservesFiniteLimits F]
    (X : ContAction FintypeCat.{u} G)
    [Nonempty
      ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X)] :
    Nonempty (F.obj X) := by
  let C := ContAction FintypeCat.{u} G
  let : PreservesLimit (Functor.empty.{0} C) (forget C) := by
    change PreservesLimit (Functor.empty.{0} C)
      (forget₂ C FintypeCat ⋙ FintypeCat.incl)
    infer_instance
  let : Unique ((forget C).obj (⊤_ C)) :=
    Concrete.uniqueOfTerminalOfPreserves (⊤_ C) terminalIsTerminal
  let : Unique ((forget FintypeCat.{u}).obj (⊤_ FintypeCat.{u})) :=
    Concrete.uniqueOfTerminalOfPreserves
      (⊤_ FintypeCat.{u}) terminalIsTerminal
  let p : X ⟶ ⊤_ C := terminal.from X
  have hp : Function.Surjective p := by
    intro y
    exact ⟨Classical.arbitrary
      ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X),
      Subsingleton.elim _ _⟩
  let : Epi p := ConcreteCategory.epi_of_surjective p hp
  let : F.PreservesEpimorphisms := by infer_instance
  let : Epi (F.map p) := Functor.map_epi F p
  have hs : Function.Surjective (F.map p) :=
    ConcreteCategory.surjective_of_epi_of_preservesPushout (F.map p)
  obtain ⟨x, -⟩ :=
    hs ((PreservesTerminal.iso F).inv
      (default : (⊤_ FintypeCat.{u})))
  exact ⟨x⟩

private instance quotientFiber_finite
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    (H : OpenKernel G) :
    Finite ((quotientFibers G F).obj H) := by
  change Finite (F.obj (quotientObject G H)).obj
  infer_instance

private instance quotientFiber_nonempty
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteColimits F] [PreservesFiniteLimits F]
    (H : OpenKernel G) :
    Nonempty ((quotientFibers G F).obj H) := by
  dsimp only [quotientFibers, Functor.comp_obj, FintypeCat.incl_obj]
  let : Nonempty
      ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj
        (quotientObject G H)) := by
    change Nonempty (G ⧸ H.toOpenNormalSubgroup.toSubgroup)
    infer_instance
  apply nonempty_image_of_nonempty G F (quotientObject G H)

private noncomputable def coherentPoint
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteColimits F] [PreservesFiniteLimits F] :
    (quotientFibers G F).sections := by
  let h :=
    nonempty_sections_of_finite_cofiltered_system (quotientFibers G F)
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

private instance carrierMulAction
    (X : ContAction FintypeCat.{u} G) :
    MulAction G
      ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X) :=
  inferInstanceAs <| MulAction G X.obj.V

private instance carrierContinuousSMul
    (X : ContAction FintypeCat.{u} G) :
    ContinuousSMul G
      ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X) := by
  change ContinuousSMul G
    ((forget₂ (Action FintypeCat.{u} G) TopCat).obj X.obj)
  exact X.property

omit [IsTopologicalGroup G] in
private theorem actionKernel_isOpen
    (X : ContAction FintypeCat.{u} G) :
    IsOpen
      ((MulAction.toPermHom G
        ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X)).ker :
          Set G) := by
  let S := (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X
  let a : G →* Equiv.Perm S := MulAction.toPermHom G S
  have hker :
      (a.ker : Set G) =
        ⋂ x : S, (MulAction.stabilizer G x : Set G) := by
    ext g
    simp only [Set.mem_iInter]
    constructor
    · intro hg x
      change a g = 1 at hg
      change g • x = x
      have hx := congrArg (fun e : Equiv.Perm S => e x) hg
      change g • x = x at hx
      exact hx
    · intro hg
      change a g = 1
      ext x
      have hx := hg x
      change g • x = x at hx
      exact hx
  change IsOpen (a.ker : Set G)
  rw [hker]
  exact isOpen_iInter_of_finite fun x => stabilizer_isOpen G x

private def actionKernelIndex
    (X : ContAction FintypeCat.{u} G) : OpenKernel G where
  val :=
    { toOpenSubgroup :=
        { toSubgroup :=
            (MulAction.toPermHom G
              ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X)).ker
          isOpen' := actionKernel_isOpen G X }
      isNormal' := by infer_instance }
  property :=
    Subgroup.finiteIndex_ker
      (MulAction.toPermHom G
        ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X))

private noncomputable def evaluation
    (X : ContAction FintypeCat.{u} G)
    (x : (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X) :
    quotientObject G (actionKernelIndex G X) ⟶ X := by
  let K := (actionKernelIndex G X).toOpenNormalSubgroup.toSubgroup
  let φ : G ⧸ K →
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X :=
    fun q => Quotient.liftOn' q (fun g : G => g • x) (by
      intro a b hab
      have hk : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
      have hperm :
          (MulAction.toPermHom G
            ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X))
              (a⁻¹ * b) = 1 :=
        hk
      have hfix : (a⁻¹ * b) • x = x := by
        have hx := congrArg
          (fun e : Equiv.Perm
            ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X) => e x)
          hperm
        exact hx
      calc
        a • x = a • ((a⁻¹ * b) • x) := congrArg (a • ·) hfix.symm
        _ = b • x := by rw [smul_smul, mul_inv_cancel_left])
  have φ_smul (g : G) (q : G ⧸ K) :
      φ (g • q) = g • φ q := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K q
    exact mul_smul g a x
  exact ObjectProperty.homMk
    { hom := FintypeCat.homMk φ
      comm := fun g => by
        ext q
        exact φ_smul g q }

private theorem evaluation_common_refinement
    {X Y : ContAction FintypeCat.{u} G} (f : X ⟶ Y)
    (x : (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X) :
    quotientMap G
          (homOfLE inf_le_left :
            actionKernelIndex G X ⊓ actionKernelIndex G Y ⟶
              actionKernelIndex G X) ≫
        evaluation G X x ≫ f =
      quotientMap G
          (homOfLE inf_le_right :
            actionKernelIndex G X ⊓ actionKernelIndex G Y ⟶
              actionKernelIndex G Y) ≫
        evaluation G Y
          ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).map f x) := by
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  ext q
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (actionKernelIndex G X ⊓
        actionKernelIndex G Y).toOpenNormalSubgroup.toSubgroup q
  change
    ConcreteCategory.hom f.hom.hom
        (ConcreteCategory.hom (X.obj.ρ g) x) =
      ConcreteCategory.hom (Y.obj.ρ g)
        (ConcreteCategory.hom f.hom.hom x)
  exact ConcreteCategory.congr_hom (f.hom.comm g) x

private noncomputable def fiberComparisonApp
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteColimits F] [PreservesFiniteLimits F]
    (X : ContAction FintypeCat.{u} G) :
    (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X ⟶ F.obj X :=
  FintypeCat.homMk fun x =>
    F.map (evaluation G X x)
      ((coherentPoint G F).val (actionKernelIndex G X))

private noncomputable def fiberComparison
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteColimits F] [PreservesFiniteLimits F] :
    forget₂ (ContAction FintypeCat.{u} G) FintypeCat ⟶ F where
  app := fiberComparisonApp G F
  naturality {X Y} f := by
    ext x
    let HX := actionKernelIndex G X
    let HY := actionKernelIndex G Y
    let L := HX ⊓ HY
    let pX : L ⟶ HX := homOfLE inf_le_left
    let pY : L ⟶ HY := homOfLE inf_le_right
    let γ := coherentPoint G F
    let γL : (F.obj (quotientObject G L)).obj := γ.val L
    have hγX :
        F.map (quotientMap G pX) γL = γ.val HX := by
      exact γ.property pX
    have hγY :
        F.map (quotientMap G pY) γL = γ.val HY := by
      exact γ.property pY
    have heval :
        quotientMap G pX ≫ evaluation G X x ≫ f =
          quotientMap G pY ≫ evaluation G Y
            ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).map f x) := by
      exact evaluation_common_refinement G f x
    change
      F.map
          (evaluation G Y
            ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).map f x))
          (γ.val HY) =
        F.map f
          (F.map (evaluation G X x) (γ.val HX))
    rw [← hγX, ← hγY]
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (F.congr_map heval.symm) γL

private noncomputable def rightEndHomOnG (H : OpenKernel G) :
    G →* End (quotientObject G H) where
  toFun g :=
    ObjectProperty.homMk <|
      Action.FintypeCat.toEndHom
        H.toOpenNormalSubgroup.toSubgroup g
  map_one' := by
    apply ObjectProperty.hom_ext
    exact
      (Action.FintypeCat.toEndHom
        H.toOpenNormalSubgroup.toSubgroup).map_one
  map_mul' g h := by
    apply ObjectProperty.hom_ext
    exact
      (Action.FintypeCat.toEndHom
        H.toOpenNormalSubgroup.toSubgroup).map_mul g h

private noncomputable def rightEndHom (H : OpenKernel G) :
    G ⧸ H.toOpenNormalSubgroup.toSubgroup →*
      End (quotientObject G H) :=
  QuotientGroup.lift H.toOpenNormalSubgroup.toSubgroup
    (rightEndHomOnG G H) (by
      intro g hg
      apply ObjectProperty.hom_ext
      exact Action.FintypeCat.toEndHom_trivial_of_mem hg)

@[simp]
private theorem rightEndHom_mk_apply
    (H : OpenKernel G) (g a : G) :
    ((rightEndHom G H (QuotientGroup.mk g)).hom.hom :
      G ⧸ H.toOpenNormalSubgroup.toSubgroup →
        G ⧸ H.toOpenNormalSubgroup.toSubgroup)
      (QuotientGroup.mk a) =
        QuotientGroup.mk (a * g⁻¹) :=
  rfl

private noncomputable def rightActionDiagram (H : OpenKernel G) :
    SingleObj (G ⧸ H.toOpenNormalSubgroup.toSubgroup) ⥤
      ContAction FintypeCat.{u} G :=
  SingleObj.functor (rightEndHom G H)

private noncomputable instance hasRightActionColimits
    (H : OpenKernel G) :
    HasColimitsOfShape
      (SingleObj (G ⧸ H.toOpenNormalSubgroup.toSubgroup))
      (ContAction FintypeCat.{u} G) := by
  obtain ⟨R, _, _, ⟨e⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv
      (G ⧸ H.toOpenNormalSubgroup.toSubgroup)
  exact Limits.hasColimitsOfShape_of_equivalence
    e.toSingleObjEquiv.symm

private noncomputable instance preservesRightActionColimits
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteColimits F] (H : OpenKernel G) :
    PreservesColimitsOfShape
      (SingleObj (G ⧸ H.toOpenNormalSubgroup.toSubgroup)) F := by
  obtain ⟨R, _, _, ⟨e⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv
      (G ⧸ H.toOpenNormalSubgroup.toSubgroup)
  exact Limits.preservesColimitsOfShape_of_equiv
    e.toSingleObjEquiv.symm F

private noncomputable instance preservesRightActionColimitsToType
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteColimits F] (H : OpenKernel G) :
    PreservesColimitsOfShape
      (SingleObj (G ⧸ H.toOpenNormalSubgroup.toSubgroup))
      (F ⋙ FintypeCat.incl) := by
  obtain ⟨R, _, _, ⟨e⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv
      (G ⧸ H.toOpenNormalSubgroup.toSubgroup)
  exact Limits.preservesColimitsOfShape_of_equiv
    e.toSingleObjEquiv.symm (F ⋙ FintypeCat.incl)

@[simp]
private theorem rightEndHom_apply
    (H : OpenKernel G)
    (r q : G ⧸ H.toOpenNormalSubgroup.toSubgroup) :
    ((rightEndHom G H r).hom.hom :
      G ⧸ H.toOpenNormalSubgroup.toSubgroup →
        G ⧸ H.toOpenNormalSubgroup.toSubgroup) q =
      q * r⁻¹ := by
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective
      H.toOpenNormalSubgroup.toSubgroup r
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      H.toOpenNormalSubgroup.toSubgroup q
  rfl

private theorem quotient_right_pretransitive (H : OpenKernel G) :
    let J :=
      rightActionDiagram G H ⋙
        forget₂ (ContAction FintypeCat.{u} G) FintypeCat ⋙
          FintypeCat.incl
    MulAction.IsPretransitive
      (G ⧸ H.toOpenNormalSubgroup.toSubgroup)
      (J.obj (SingleObj.star
        (G ⧸ H.toOpenNormalSubgroup.toSubgroup))) := by
  dsimp only
  constructor
  intro x y
  change G ⧸ H.toOpenNormalSubgroup.toSubgroup at x y
  refine ⟨y⁻¹ * x, ?_⟩
  change
    ((rightEndHom G H (y⁻¹ * x)).hom.hom :
      G ⧸ H.toOpenNormalSubgroup.toSubgroup →
        G ⧸ H.toOpenNormalSubgroup.toSubgroup) x = y
  rw [rightEndHom_apply]
  group
  rfl

private noncomputable def rightActionColimitTerminal
    (H : OpenKernel G) :
    IsTerminal (colimit (rightActionDiagram G H)) := by
  let C := ContAction FintypeCat.{u} G
  let U := forget₂ C FintypeCat
  let R := G ⧸ H.toOpenNormalSubgroup.toSubgroup
  let J := rightActionDiagram G H
  let JT := J ⋙ U ⋙ FintypeCat.incl
  have hpre :
      MulAction.IsPretransitive R
        (JT.obj (SingleObj.star R)) :=
    quotient_right_pretransitive G H
  letI : Nonempty (JT.obj (SingleObj.star R)) := by
    change Nonempty R
    infer_instance
  letI : Unique
      (MulAction.orbitRel.Quotient R
        (JT.obj (SingleObj.star R))) :=
    Classical.choice <|
      (MulAction.pretransitive_iff_unique_quotient_of_nonempty
        R (JT.obj (SingleObj.star R))).mp hpre
  let e :
      (U.obj (colimit J) : Type u) ≃
        MulAction.orbitRel.Quotient R
          (JT.obj (SingleObj.star R)) :=
    (preservesColimitIso (U ⋙ FintypeCat.incl) J ≪≫
      Equiv.toIso (SingleObj.Types.colimitEquivQuotient JT)).toEquiv
  let y₀ : (colimit J).obj.V.obj := e.symm default
  refine IsTerminal.ofUniqueHom ?_ ?_
  · intro X
    exact ⟨
      { hom := FintypeCat.homMk (fun _ => y₀)
        comm := fun g => by
          apply FintypeCat.hom_ext
          intro x
          exact e.injective (Subsingleton.elim _ _) }⟩
  · intro X f
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply FintypeCat.hom_ext
    intro x
    exact e.injective (Subsingleton.elim _ _)

private theorem image_right_pretransitive
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : OpenKernel G) :
    let R := G ⧸ H.toOpenNormalSubgroup.toSubgroup
    let JF := rightActionDiagram G H ⋙ F ⋙ FintypeCat.incl
    MulAction.IsPretransitive R
      (JF.obj (SingleObj.star R)) := by
  let R := G ⧸ H.toOpenNormalSubgroup.toSubgroup
  let J := rightActionDiagram G H
  let JF := J ⋙ F ⋙ FintypeCat.incl
  have hterminal : IsTerminal (F.obj (colimit J)) :=
    IsTerminal.isTerminalObj F (colimit J)
      (rightActionColimitTerminal G H)
  let : Unique (F.obj (colimit J) : Type u) :=
    Concrete.uniqueOfTerminalOfPreserves
      (F.obj (colimit J)) hterminal
  let e :
      (F.obj (colimit J) : Type u) ≃
        MulAction.orbitRel.Quotient R
          (JF.obj (SingleObj.star R)) :=
    (preservesColimitIso (F ⋙ FintypeCat.incl) J ≪≫
      Equiv.toIso (SingleObj.Types.colimitEquivQuotient JF)).toEquiv
  let : Unique
      (MulAction.orbitRel.Quotient R
        (JF.obj (SingleObj.star R))) :=
    { default := e default
      uniq := fun x => e.symm.injective (Subsingleton.elim _ _) }
  let : Nonempty (JF.obj (SingleObj.star R)) := by
    change Nonempty (F.obj (quotientObject G H))
    exact quotientFiber_nonempty G F H
  exact
    (MulAction.pretransitive_iff_unique_quotient_of_nonempty
      R (JF.obj (SingleObj.star R))).mpr ⟨inferInstance⟩

private noncomputable def finiteEqualizerEquiv
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F]
    {X Y : ContAction FintypeCat.{u} G} (f g : X ⟶ Y) :
    F.obj (equalizer f g) ≃
      { x : F.obj X // F.map f x = F.map g x } :=
  (PreservesEqualizer.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.equalizerIso (F.map f).hom (F.map g).hom).toEquiv

private theorem rightEndHom_fixed_implies_one
    (H : OpenKernel G)
    (r : G ⧸ H.toOpenNormalSubgroup.toSubgroup)
    (q :
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj
        (quotientObject G H))
    (hq :
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).map
        (rightEndHom G H r) q = q) :
    r = 1 := by
  change G ⧸ H.toOpenNormalSubgroup.toSubgroup at q
  change
    ((rightEndHom G H r).hom.hom :
      (G ⧸ H.toOpenNormalSubgroup.toSubgroup) →
        (G ⧸ H.toOpenNormalSubgroup.toSubgroup)) q = q at hq
  rw [rightEndHom_apply] at hq
  have hq' : q * r⁻¹ = q * 1 :=
    hq.trans (mul_one q).symm
  exact inv_eq_one.mp (mul_left_cancel hq')

private theorem image_right_fixed_implies_one
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : OpenKernel G)
    (r : G ⧸ H.toOpenNormalSubgroup.toSubgroup)
    (s : F.obj (quotientObject G H))
    (hs : F.map (rightEndHom G H r) s = s) :
    r = 1 := by
  by_contra hr
  let C := ContAction FintypeCat.{u} G
  let U := forget₂ C FintypeCat
  let e : End (quotientObject G H) := rightEndHom G H r
  let E := equalizer e (𝟙 (quotientObject G H))
  have hemptyU : IsEmpty (U.obj E) := by
    constructor
    intro z
    let z' := finiteEqualizerEquiv G U e
      (𝟙 (quotientObject G H)) z
    have hz := z'.property
    apply hr
    apply rightEndHom_fixed_implies_one G H r z'.val
    simpa [e] using hz
  have hEinitial : IsInitial E := by
    refine IsInitial.ofUniqueHom ?_ ?_
    · intro Y
      exact ⟨
        { hom := FintypeCat.homMk (fun x => (hemptyU.false x).elim)
          comm := fun g => by
            apply FintypeCat.hom_ext
            intro x
            exact (hemptyU.false x).elim }⟩
    · intro Y f
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      apply FintypeCat.hom_ext
      intro x
      exact (hemptyU.false x).elim
  have hFEinitial : IsInitial (F.obj E) :=
    IsInitial.isInitialObj F E hEinitial
  have hemptyF : IsEmpty (F.obj E) :=
    Concrete.empty_of_initial_of_preserves
      (F.obj E) ⟨hFEinitial⟩
  apply hemptyF.false
  exact
    (finiteEqualizerEquiv G F e
      (𝟙 (quotientObject G H))).symm
        ⟨s, by simpa [e] using hs⟩

private theorem image_right_transitive
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : OpenKernel G)
    (x y : F.obj (quotientObject G H)) :
    ∃ r : G ⧸ H.toOpenNormalSubgroup.toSubgroup,
      F.map (rightEndHom G H r) x = y := by
  let R := G ⧸ H.toOpenNormalSubgroup.toSubgroup
  let JF := rightActionDiagram G H ⋙ F ⋙ FintypeCat.incl
  have hpre :
      MulAction.IsPretransitive R
        (JF.obj (SingleObj.star R)) :=
    image_right_pretransitive G F H
  rcases hpre.exists_smul_eq x y with ⟨r, hr⟩
  exact ⟨r, hr⟩

private theorem fiberComparison_right_equivariant
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : OpenKernel G)
    (r : G ⧸ H.toOpenNormalSubgroup.toSubgroup)
    (q :
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj
        (quotientObject G H)) :
    fiberComparisonApp G F (quotientObject G H)
        ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).map
          (rightEndHom G H r) q) =
      F.map (rightEndHom G H r)
        (fiberComparisonApp G F (quotientObject G H) q) := by
  exact ConcreteCategory.congr_hom
    ((fiberComparison G F).naturality (rightEndHom G H r)) q

private theorem fiberComparison_quotient_bijective
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : OpenKernel G) :
    Function.Bijective
      (fiberComparisonApp G F (quotientObject G H)) := by
  let U := forget₂
    (ContAction FintypeCat.{u} G) FintypeCat
  let t := fiberComparisonApp G F (quotientObject G H)
  constructor
  · intro q₁ q₂ hq
    obtain ⟨r, hr⟩ :=
      quotient_right_pretransitive G H |>.exists_smul_eq q₁ q₂
    have hr' :
        U.map (rightEndHom G H r) q₁ = q₂ := hr
    have hfixed :
        F.map (rightEndHom G H r) (t q₁) = t q₁ := by
      calc
        F.map (rightEndHom G H r) (t q₁) =
            t (U.map (rightEndHom G H r) q₁) :=
          (fiberComparison_right_equivariant G F H r q₁).symm
        _ = t q₂ := congrArg t hr'
        _ = t q₁ := hq.symm
    have hrone :=
      image_right_fixed_implies_one G F H r (t q₁) hfixed
    subst r
    simpa using hr'
  · intro y
    let q₀ :
        (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj
          (quotientObject G H) :=
      QuotientGroup.mk 1
    obtain ⟨r, hr⟩ :=
      image_right_transitive G F H (t q₀) y
    refine ⟨U.map (rightEndHom G H r) q₀, ?_⟩
    exact
      (fiberComparison_right_equivariant G F H r q₀).trans hr

private noncomputable def copiesDiagram
    (X : ContAction FintypeCat.{u} G) :
    Discrete
        ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X) ⥤
      ContAction FintypeCat.{u} G :=
  Discrete.functor fun _ =>
    quotientObject G (actionKernelIndex G X)

private noncomputable abbrev copiesObject
    (X : ContAction FintypeCat.{u} G) :
    ContAction FintypeCat.{u} G :=
  colimit (copiesDiagram G X)

private noncomputable def copiesCover
    (X : ContAction FintypeCat.{u} G) :
    copiesObject G X ⟶ X :=
  colimit.desc (copiesDiagram G X) <|
    Cofan.mk X fun x => evaluation G X x

@[reassoc (attr := simp)]
private theorem copies_ι_cover
    (X : ContAction FintypeCat.{u} G)
    (x : (forget₂
      (ContAction FintypeCat.{u} G) FintypeCat).obj X) :
    colimit.ι (copiesDiagram G X) ⟨x⟩ ≫ copiesCover G X =
      evaluation G X x := by
  exact colimit.ι_desc
    (Cofan.mk X fun x => evaluation G X x) ⟨x⟩

@[simp]
private theorem evaluation_one
    (X : ContAction FintypeCat.{u} G)
    (x : (forget₂
      (ContAction FintypeCat.{u} G) FintypeCat).obj X) :
    (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).map
        (evaluation G X x)
        (QuotientGroup.mk 1) = x := by
  change (1 : G) • x = x
  exact one_smul G x

private theorem copiesCover_surjective
    (X : ContAction FintypeCat.{u} G) :
    Function.Surjective (copiesCover G X) := by
  let U := forget₂
    (ContAction FintypeCat.{u} G) FintypeCat
  intro x
  let q₀ :
      U.obj (quotientObject G (actionKernelIndex G X)) :=
    QuotientGroup.mk 1
  refine
    ⟨U.map (colimit.ι (copiesDiagram G X) ⟨x⟩) q₀, ?_⟩
  exact
    (ConcreteCategory.congr_hom (copies_ι_cover G X x) q₀).trans
      (evaluation_one G X x)

private theorem fiberComparison_copies_isIso
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : ContAction FintypeCat.{u} G) :
    IsIso
      ((fiberComparison G F).app (copiesObject G X)) := by
  let t := fiberComparison G F
  let D := copiesDiagram G X
  let (j : Discrete
      ((forget₂
        (ContAction FintypeCat.{u} G) FintypeCat).obj X)) :
      IsIso ((Functor.whiskerLeft D t).app j) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact fiberComparison_quotient_bijective G F
      (actionKernelIndex G X)
  let : IsIso (Functor.whiskerLeft D t) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit
    D t (colimit.cocone D) (colimit.isColimit D)

private noncomputable def finitePullbackEquiv
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F]
    {X A B : ContAction FintypeCat.{u} G}
    (f : A ⟶ X) (g : B ⟶ X) :
    F.obj (pullback f g) ≃
      { p : F.obj A × F.obj B //
        F.map f p.1 = F.map g p.2 } :=
  (PreservesPullback.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.pullbackIsoPullback (F.map f).hom (F.map g).hom).toEquiv

omit [IsTopologicalGroup G] in
@[simp]
private theorem finitePullbackEquiv_symm_fst_apply
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F]
    {X A B : ContAction FintypeCat.{u} G}
    {f : A ⟶ X} {g : B ⟶ X}
    (a : F.obj A) (b : F.obj B)
    (h : F.map f a = F.map g b) :
    F.map (pullback.fst f g)
        ((finitePullbackEquiv G F f g).symm
          ⟨(a, b), h⟩) = a := by
  simp only [finitePullbackEquiv, Functor.comp_map,
    Iso.toEquiv_comp]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.fst f g)) _ = _
  erw [PreservesPullback.iso_inv_fst,
    Types.pullbackIsoPullback_inv_fst]
  rfl

omit [IsTopologicalGroup G] in
@[simp]
private theorem finitePullbackEquiv_symm_snd_apply
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F]
    {X A B : ContAction FintypeCat.{u} G}
    {f : A ⟶ X} {g : B ⟶ X}
    (a : F.obj A) (b : F.obj B)
    (h : F.map f a = F.map g b) :
    F.map (pullback.snd f g)
        ((finitePullbackEquiv G F f g).symm
          ⟨(a, b), h⟩) = b := by
  simp only [finitePullbackEquiv, Functor.comp_map,
    Iso.toEquiv_comp]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.snd f g)) _ = _
  erw [PreservesPullback.iso_inv_snd,
    Types.pullbackIsoPullback_inv_snd]
  rfl

private theorem fiberComparison_surjective
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : ContAction FintypeCat.{u} G) :
    Function.Surjective
      ((fiberComparison G F).app X) := by
  let C := ContAction FintypeCat.{u} G
  let U := forget₂ C FintypeCat
  let t := fiberComparison G F
  let P := copiesObject G X
  let p : P ⟶ X := copiesCover G X
  have hp : Function.Surjective p :=
    copiesCover_surjective G X
  let : Epi p :=
    ConcreteCategory.epi_of_surjective p hp
  let : F.PreservesEpimorphisms := by
    infer_instance
  let : Epi (F.map p) :=
    Functor.map_epi F p
  have hFp : Function.Surjective (F.map p) :=
    ConcreteCategory.surjective_of_epi_of_preservesPushout
      (F.map p)
  let : IsIso (t.app P) :=
    fiberComparison_copies_isIso G F X
  have htP : Function.Bijective (t.app P) :=
    ConcreteCategory.bijective_of_isIso (t.app P)
  intro y
  obtain ⟨z, hz⟩ := hFp y
  obtain ⟨a, ha⟩ := htP.2 z
  refine ⟨U.map p a, ?_⟩
  calc
    t.app X (U.map p a) =
        F.map p (t.app P a) :=
      ConcreteCategory.congr_hom (t.naturality p) a
    _ = F.map p z := congrArg (F.map p) ha
    _ = y := hz

private theorem fiberComparison_injective
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : ContAction FintypeCat.{u} G) :
    Function.Injective
      ((fiberComparison G F).app X) := by
  let C := ContAction FintypeCat.{u} G
  let U := forget₂ C FintypeCat
  let t := fiberComparison G F
  let P := copiesObject G X
  let p : P ⟶ X := copiesCover G X
  have hp : Function.Surjective p :=
    copiesCover_surjective G X
  let : IsIso (t.app P) :=
    fiberComparison_copies_isIso G F X
  have htP : Function.Bijective (t.app P) :=
    ConcreteCategory.bijective_of_isIso (t.app P)
  intro x₁ x₂ hx
  obtain ⟨a, ha⟩ := hp x₁
  obtain ⟨b, hb⟩ := hp x₂
  have habF :
      F.map p (t.app P a) =
        F.map p (t.app P b) := by
    calc
      F.map p (t.app P a) =
          t.app X (U.map p a) :=
        (ConcreteCategory.congr_hom
          (t.naturality p) a).symm
      _ = t.app X x₁ := congrArg (t.app X) ha
      _ = t.app X x₂ := hx
      _ = t.app X (U.map p b) :=
        congrArg (t.app X) hb.symm
      _ = F.map p (t.app P b) :=
        ConcreteCategory.congr_hom
          (t.naturality p) b
  let R := pullback p p
  let zF : F.obj R :=
    (finitePullbackEquiv G F p p).symm
      ⟨(t.app P a, t.app P b), habF⟩
  obtain ⟨z, hz⟩ :=
    fiberComparison_surjective G F R zF
  have hfstT :
      t.app P (U.map (pullback.fst p p) z) =
        t.app P a := by
    calc
      t.app P (U.map (pullback.fst p p) z) =
          F.map (pullback.fst p p) (t.app R z) :=
        ConcreteCategory.congr_hom
          (t.naturality (pullback.fst p p)) z
      _ = F.map (pullback.fst p p) zF :=
        congrArg (F.map (pullback.fst p p)) hz
      _ = t.app P a :=
        finitePullbackEquiv_symm_fst_apply
          G F (t.app P a) (t.app P b) habF
  have hsndT :
      t.app P (U.map (pullback.snd p p) z) =
        t.app P b := by
    calc
      t.app P (U.map (pullback.snd p p) z) =
          F.map (pullback.snd p p) (t.app R z) :=
        ConcreteCategory.congr_hom
          (t.naturality (pullback.snd p p)) z
      _ = F.map (pullback.snd p p) zF :=
        congrArg (F.map (pullback.snd p p)) hz
      _ = t.app P b :=
        finitePullbackEquiv_symm_snd_apply
          G F (t.app P a) (t.app P b) habF
  have hfst :
      U.map (pullback.fst p p) z = a :=
    htP.1 hfstT
  have hsnd :
      U.map (pullback.snd p p) z = b :=
    htP.1 hsndT
  have hcond :=
    ConcreteCategory.congr_hom
      (pullback.condition : pullback.fst p p ≫ p =
        pullback.snd p p ≫ p) z
  change
    U.map p (U.map (pullback.fst p p) z) =
      U.map p (U.map (pullback.snd p p) z) at hcond
  rw [hfst, hsnd] at hcond
  exact ha.symm.trans (hcond.trans hb)

private theorem fiberComparison_bijective
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : ContAction FintypeCat.{u} G) :
    Function.Bijective
      ((fiberComparison G F).app X) :=
  ⟨fiberComparison_injective G F X,
    fiberComparison_surjective G F X⟩

@[stacks 0BMV]
theorem nonempty_iso_forget_of_exact
    (F : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u})
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Nonempty
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat ≅ F) := by
  let t := fiberComparison G F
  let (X : ContAction FintypeCat.{u} G) :
      IsIso (t.app X) :=
    (ConcreteCategory.isIso_iff_bijective
      (t.app X)).mpr
        (fiberComparison_bijective G F X)
  let : IsIso t :=
    NatIso.isIso_of_isIso_app t
  exact ⟨asIso t⟩

end CategoryTheory.FiniteContinuousAction
