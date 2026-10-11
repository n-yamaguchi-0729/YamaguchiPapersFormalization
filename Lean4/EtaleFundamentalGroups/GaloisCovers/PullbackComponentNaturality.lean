/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.PullbackComponent
import EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
import EtaleFundamentalGroups.GeometricFiber.FundamentalGroupComposition
import EtaleFundamentalGroups.GeometricFiber.PointedCover
import EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint
import ProCGroups.FiniteStepSolvableQuotients.ProsolvableCriterion
import ProCGroups.Topologies.Conjugation

/-!
# Fundamental-group squares from pointed pullback components

A connected Galois component containing the chosen point of a pulled-back
Galois cover realizes the restriction of the original fundamental-group map.
The unavoidable comparison between two factorizations is an inner
automorphism.  Normality of the target stabilizer absorbs this conjugation and
produces a strictly commuting square of topological groups.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

private noncomputable def subgroupContinuousMulEquivOfEq
    {G : Type u} [TopologicalSpace G] [Group G]
    {H K : Subgroup G} (h : H = K) : H ≃ₜ* K := by
  subst K
  exact ContinuousMulEquiv.refl H

private theorem subgroupContinuousMulEquivOfEq_coe
    {G : Type u} [TopologicalSpace G] [Group G]
    {H K : Subgroup G} (h : H = K) (x : H) :
    ((subgroupContinuousMulEquivOfEq h x : K) : G) = x := by
  subst K
  rfl

private theorem restrictPreimage_coe
    {G Q : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (f : G →ₜ* Q) (H : Subgroup Q)
    (x : H.comap f.toMonoidHom) :
    ((ProCGroups.ContinuousMonoidHom.restrictPreimage f H x : H) : Q) = f x :=
  rfl

variable {Omega : Type u} [Field Omega]

private theorem fundamentalGroupHom_transport_source
    {S T : Scheme.{u}} (f : S ⟶ T)
    {xi xi' : Spec (.of Omega) ⟶ S} (hxi : xi = xi')
    (a : π₁ᵉᵗ(xi)) :
    (congrArg (fun q ↦ q ≫ f) hxi) ▸ fundamentalGroupHom f xi a =
      fundamentalGroupHom f xi' (hxi ▸ a) := by
  subst xi'
  rfl

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable [IsSepClosed Omega]

/-- Actual pointed component data of a pulled-back Galois cover produces a
strictly commuting square between its fundamental groups and the preimage of
the target point stabilizer. -/
theorem exists_fundamentalGroup_square_of_galoisPullbackComponent
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (hA : IsGalois A)
    (x : (fiber (xi ≫ f)).obj A)
    (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj A)
    (z : (fiber xi).obj Z)
    (hiz : (fiber xi).map i z =
      transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x)
    (hi : Mono i) :
    let xiZ := (fiberObjEquivHom xi Z z).left
    let g := i.left ≫ Limits.pullback.fst A.hom f
    ∃ (eSource : π₁ᵉᵗ(xiZ) ≃ₜ*
        (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
          (fundamentalGroupHom f xi).toMonoidHom)
      (eTarget : π₁ᵉᵗ(xiZ ≫ g) ≃ₜ*
        MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x),
      ∀ a,
        eTarget (fundamentalGroupHom g xiZ a) =
          ProCGroups.ContinuousMonoidHom.restrictPreimage
            (fundamentalGroupHom f xi)
            (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x) (eSource a) := by
  dsimp only
  let : Mono i := hi
  let : IsGalois A := hA
  let y : (fiber xi).obj ((pullback f).obj A) :=
    transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x
  let xiZ : Spec (.of Omega) ⟶ Z.left := (fiberObjEquivHom xi Z z).left
  let g : Z.left ⟶ A.left := i.left ≫ Limits.pullback.fst A.hom f
  have hxiZ : xiZ ≫ Z.hom = xi := (fiberObjEquivHom xi Z z).w
  have hi_injective : Function.Injective ((fiber xi).map i) := by
    let : Mono ((fiber xi).map i) := Functor.map_mono (fiber xi) i
    exact ConcreteCategory.injective_of_mono_of_preservesPullback ((fiber xi).map i)
  have hstab_component :
      MulAction.stabilizer π₁ᵉᵗ(xi) z =
        MulAction.stabilizer π₁ᵉᵗ(xi) y := by
    ext a
    simp only [MulAction.mem_stabilizer_iff]
    constructor
    · intro ha
      calc
        a • y = a • (fiber xi).map i z :=
          congrArg (fun q ↦ a • q) hiz.symm
        _ = (fiber xi).map i (a • z) :=
          mulAction_naturality (fiber xi) a i z
        _ = (fiber xi).map i z := congrArg ((fiber xi).map i) ha
        _ = y := hiz
    · intro ha
      apply hi_injective
      calc
        (fiber xi).map i (a • z) = a • (fiber xi).map i z :=
          (mulAction_naturality (fiber xi) a i z).symm
        _ = a • y := congrArg (fun q ↦ a • q) hiz
        _ = y := ha
        _ = (fiber xi).map i z := hiz.symm
  have hstab :
      MulAction.stabilizer π₁ᵉᵗ(xi) z =
        (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
          (fundamentalGroupHom f xi).toMonoidHom := by
    calc
      MulAction.stabilizer π₁ᵉᵗ(xi) z =
          MulAction.stabilizer π₁ᵉᵗ(xi) y := hstab_component
      _ = (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
          (fundamentalGroupHom f xi).toMonoidHom :=
        stabilizer_transportedPointOfCompIso
          (pullback f) (pullbackFiberIso f xi) A x
  have hliftZ :
      (fiberObjEquivHom xi Z).symm (Over.homMk xiZ hxiZ) = z := by
    apply (fiberObjEquivHom xi Z).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    rfl
  have htransportZ :
      (hxiZ ▸ MulAction.stabilizer π₁ᵉᵗ(xiZ ≫ Z.hom)
        (liftedFiberPointOverComposite Z xiZ)) =
          MulAction.stabilizer π₁ᵉᵗ(xi)
            ((fiberObjEquivHom xi Z).symm (Over.homMk xiZ hxiZ)) :=
    transported_stabilizer_liftedFiberPointOverComposite Z xiZ hxiZ
  have hSourceSub :
      (hxiZ ▸ MulAction.stabilizer π₁ᵉᵗ(xiZ ≫ Z.hom)
        (liftedFiberPointOverComposite Z xiZ)) =
        (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
          (fundamentalGroupHom f xi).toMonoidHom := by
    exact htransportZ.trans ((congrArg
      (MulAction.stabilizer π₁ᵉᵗ(xi)) hliftZ).trans hstab)
  let eSource : π₁ᵉᵗ(xiZ) ≃ₜ*
      (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
        (fundamentalGroupHom f xi).toMonoidHom :=
    (fundamentalGroupEquivStabilizerOfLiftOfEq Z xiZ hxiZ).trans
      (subgroupContinuousMulEquivOfEq hSourceSub)
  have hiw : i.left ≫ Limits.pullback.snd A.hom f = Z.hom := by
    exact MorphismProperty.Over.w i
  have hsquare : g ≫ A.hom = Z.hom ≫ f := by
    let q0 : Z.left ⟶ Y := g ≫ A.hom
    let q1 : Z.left ⟶ Y :=
      i.left ≫ (Limits.pullback.fst A.hom f ≫ A.hom)
    let q2 : Z.left ⟶ Y :=
      i.left ≫ (Limits.pullback.snd A.hom f ≫ f)
    let q3 : Z.left ⟶ Y :=
      (i.left ≫ Limits.pullback.snd A.hom f) ≫ f
    let q4 : Z.left ⟶ Y := Z.hom ≫ f
    have h01 : q0 = q1 := by
      dsimp only [q0, q1, g]
      exact Category.assoc _ _ _
    have h12 : q1 = q2 := by
      exact congrArg (fun q ↦ i.left ≫ q) Limits.pullback.condition
    have h23 : q2 = q3 := by
      dsimp only [q2, q3]
      exact (Category.assoc _ _ _).symm
    have h34 : q3 = q4 := by
      exact congrArg (fun q ↦ q ≫ f) hiw
    exact h01.trans (h12.trans (h23.trans h34))
  have hxiA : (xiZ ≫ g) ≫ A.hom = xi ≫ f := by
    calc
      (xiZ ≫ g) ≫ A.hom = xiZ ≫ (g ≫ A.hom) := Category.assoc _ _ _
      _ = xiZ ≫ (Z.hom ≫ f) := congrArg (fun q ↦ xiZ ≫ q) hsquare
      _ = (xiZ ≫ Z.hom) ≫ f := (Category.assoc _ _ _).symm
      _ = xi ≫ f := congrArg (fun q ↦ q ≫ f) hxiZ
  have hzmap : xiZ ≫ i.left =
      (fiberObjEquivHom xi ((pullback f).obj A) ((fiber xi).map i z)).left := by
    exact congrArg (fun q ↦ q.left) (fiberObjEquivHom_naturality xi i z)
  have hytransport : (pullbackFiberIso f xi).hom.app A y = x := by
    exact FintypeCat.inv_hom_id_apply ((pullbackFiberIso f xi).app A) x
  have hyprojection :
      (fiberObjEquivHom xi ((pullback f).obj A) y).left ≫
          Limits.pullback.fst A.hom f =
        (fiberObjEquivHom (xi ≫ f) A x).left := by
    have h := pullbackFiberIso_hom_fiberObjEquivHom_left f xi A y
    rw [hytransport] at h
    exact h.symm
  have hxiApoint : xiZ ≫ g = (fiberObjEquivHom (xi ≫ f) A x).left := by
    let q0 : Spec (.of Omega) ⟶ A.left := xiZ ≫ g
    let q1 : Spec (.of Omega) ⟶ A.left :=
      (xiZ ≫ i.left) ≫ Limits.pullback.fst A.hom f
    let q2 : Spec (.of Omega) ⟶ A.left :=
      (fiberObjEquivHom xi ((pullback f).obj A)
        ((fiber xi).map i z)).left ≫ Limits.pullback.fst A.hom f
    let q3 : Spec (.of Omega) ⟶ A.left :=
      (fiberObjEquivHom xi ((pullback f).obj A) y).left ≫
        Limits.pullback.fst A.hom f
    let q4 : Spec (.of Omega) ⟶ A.left :=
      (fiberObjEquivHom (xi ≫ f) A x).left
    have h01 : q0 = q1 := by
      dsimp only [q0, q1, g]
      exact (Category.assoc _ _ _).symm
    have h12 : q1 = q2 :=
      congrArg (fun q ↦ q ≫ Limits.pullback.fst A.hom f) hzmap
    have h23 : q2 = q3 := by
      exact congrArg
        (fun q ↦ (fiberObjEquivHom xi ((pullback f).obj A) q).left ≫
          Limits.pullback.fst A.hom f) hiz
    have h34 : q3 = q4 := hyprojection
    exact h01.trans (h12.trans (h23.trans h34))
  have hliftA :
      (fiberObjEquivHom (xi ≫ f) A).symm
          (Over.homMk (xiZ ≫ g) hxiA) = x := by
    apply (fiberObjEquivHom (xi ≫ f) A).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    exact hxiApoint
  have htransportA :
      (hxiA ▸ MulAction.stabilizer π₁ᵉᵗ((xiZ ≫ g) ≫ A.hom)
        (liftedFiberPointOverComposite A (xiZ ≫ g))) =
          MulAction.stabilizer π₁ᵉᵗ(xi ≫ f)
            ((fiberObjEquivHom (xi ≫ f) A).symm
              (Over.homMk (xiZ ≫ g) hxiA)) :=
    transported_stabilizer_liftedFiberPointOverComposite A (xiZ ≫ g) hxiA
  have hTargetSub :
      (hxiA ▸ MulAction.stabilizer π₁ᵉᵗ((xiZ ≫ g) ≫ A.hom)
        (liftedFiberPointOverComposite A (xiZ ≫ g))) =
          MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x := by
    exact htransportA.trans (congrArg
      (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f)) hliftA)
  let eTarget0 : π₁ᵉᵗ(xiZ ≫ g) ≃ₜ*
      MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x :=
    (fundamentalGroupEquivStabilizerOfLiftOfEq A (xiZ ≫ g) hxiA).trans
      (subgroupContinuousMulEquivOfEq hTargetSub)
  let m : Z.left ⟶ Y := Z.hom ≫ f
  have hm1 : m = g ≫ A.hom := hsquare.symm
  have hm2 : m = Z.hom ≫ f := rfl
  have hxi2 : (xiZ ≫ Z.hom) ≫ f = xi ≫ f :=
    congrArg (fun q ↦ q ≫ f) hxiZ
  let k : π₁ᵉᵗ(xi ≫ f) := fundamentalGroupFactorizationConjugator
    g A.hom Z.hom f m hm1 hm2 xiZ (xi ≫ f) hxiA hxi2
  let H : Subgroup π₁ᵉᵗ(xi ≫ f) :=
    MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x
  let : H.Normal := stabilizer_normal_of_isGalois (fiber (xi ≫ f)) A x
  let eTarget : π₁ᵉᵗ(xiZ ≫ g) ≃ₜ* H :=
    eTarget0.trans (ProCGroups.Subgroup.conjNormalContinuousMulEquiv H k⁻¹)
  refine ⟨eSource, eTarget, ?_⟩
  intro a
  apply Subtype.ext
  have hSourceCoe :
      ((eSource a :
          (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
            (fundamentalGroupHom f xi).toMonoidHom) : π₁ᵉᵗ(xi)) =
        hxiZ ▸ fundamentalGroupHom Z.hom xiZ a := by
    dsimp only [eSource, ContinuousMulEquiv.trans_apply]
    rw [subgroupContinuousMulEquivOfEq_coe]
    exact fundamentalGroupEquivStabilizerOfLiftOfEq_coe Z xiZ hxiZ a
  have hTargetCoe (b : π₁ᵉᵗ(xiZ ≫ g)) :
      ((eTarget0 b : MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x) :
          π₁ᵉᵗ(xi ≫ f)) =
        hxiA ▸ fundamentalGroupHom A.hom (xiZ ≫ g) b := by
    dsimp only [eTarget0, ContinuousMulEquiv.trans_apply]
    rw [subgroupContinuousMulEquivOfEq_coe]
    exact fundamentalGroupEquivStabilizerOfLiftOfEq_coe
      A (xiZ ≫ g) hxiA b
  have htransportF :
      hxi2 ▸ fundamentalGroupHom f (xiZ ≫ Z.hom)
          (fundamentalGroupHom Z.hom xiZ a) =
        fundamentalGroupHom f xi (hxiZ ▸
          fundamentalGroupHom Z.hom xiZ a) := by
    exact fundamentalGroupHom_transport_source f hxiZ
      (fundamentalGroupHom Z.hom xiZ a)
  have hfactor := fundamentalGroupHom_comp_conj_of_common_composite
    g A.hom Z.hom f m hm1 hm2 xiZ (xi ≫ f) hxiA hxi2 a
  have hfactor' :
      ((eTarget0 (fundamentalGroupHom g xiZ a) : H) : π₁ᵉᵗ(xi ≫ f)) =
        MulAut.conj k
          (fundamentalGroupHom f xi ((eSource a : _) : π₁ᵉᵗ(xi))) := by
    rw [hTargetCoe, hSourceCoe, ← htransportF]
    exact hfactor
  change ((eTarget (fundamentalGroupHom g xiZ a) : H) :
      π₁ᵉᵗ(xi ≫ f)) =
    fundamentalGroupHom f xi ((eSource a : _) : π₁ᵉᵗ(xi))
  dsimp only [eTarget, ContinuousMulEquiv.trans_apply,
    ProCGroups.Subgroup.conjNormalContinuousMulEquiv_apply]
  rw [MulAut.conjNormal_apply, hfactor']
  simp [MulAut.conj_apply, mul_assoc]

/-- Choosing the connected Galois component supplied by
`exists_galoisComponent_pullback` gives the strict fundamental-group square
without any abstract naturality hypothesis. -/
theorem exists_galoisPullbackComponent_fundamentalGroup_square
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (hA : IsGalois A)
    (x : (fiber (xi ≫ f)).obj A) :
    ∃ (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj A)
      (z : (fiber xi).obj Z),
      IsGalois Z ∧ Mono i ∧
        let xiZ := (fiberObjEquivHom xi Z z).left
        let g := i.left ≫ Limits.pullback.fst A.hom f
        ∃ (eSource : π₁ᵉᵗ(xiZ) ≃ₜ*
            (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
              (fundamentalGroupHom f xi).toMonoidHom)
          (eTarget : π₁ᵉᵗ(xiZ ≫ g) ≃ₜ*
            MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x),
          ∀ a,
            eTarget (fundamentalGroupHom g xiZ a) =
              ProCGroups.ContinuousMonoidHom.restrictPreimage
                (fundamentalGroupHom f xi)
                (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x) (eSource a) := by
  obtain ⟨Z, i, z, hiz, hZ, hi⟩ :=
    exists_galoisComponent_pullback f xi A hA x
  refine ⟨Z, i, z, hZ, hi, ?_⟩
  exact exists_fundamentalGroup_square_of_galoisPullbackComponent
    f xi A hA x Z i z hiz hi

/-- Every open normal subgroup of the target fundamental group is realized by
an actual pointed Galois cover and an actual pointed connected component of
its pullback.  The resulting fundamental-group square commutes strictly. -/
theorem exists_openNormal_galoisPullbackComponent_fundamentalGroup_square
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ f)) :
    ∃ (A : FiniteEtale Y) (_x : (fiber (xi ≫ f)).obj A)
      (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj A)
      (z : (fiber xi).obj Z),
      IsGalois A ∧ IsGalois Z ∧ Mono i ∧
        let xiZ := (fiberObjEquivHom xi Z z).left
        let g := i.left ≫ Limits.pullback.fst A.hom f
        ∃ (eSource : π₁ᵉᵗ(xiZ) ≃ₜ*
            ProCGroups.OpenNormalSubgroup.comap
              (fundamentalGroupHom f xi).toMonoidHom
              (fundamentalGroupHom f xi).continuous_toFun U)
          (eTarget : π₁ᵉᵗ(xiZ ≫ g) ≃ₜ* U),
          ∀ a,
            eTarget (fundamentalGroupHom g xiZ a) =
              ProCGroups.ContinuousMonoidHom.restrictPreimage
                (fundamentalGroupHom f xi)
                (U : Subgroup π₁ᵉᵗ(xi ≫ f)) (eSource a) := by
  obtain ⟨A, hA, x, hx⟩ :=
    exists_galois_object_point_stabilizer_eq_any_universe
      (C := FiniteEtale Y) (fiber (xi ≫ f)) U
  obtain ⟨Z, i, z, hZ, hi, hsq⟩ :=
    exists_galoisPullbackComponent_fundamentalGroup_square f xi A hA x
  dsimp only at hsq
  obtain ⟨eSource, eTarget, hcomm⟩ := hsq
  have hSourceSub :
      (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
          (fundamentalGroupHom f xi).toMonoidHom =
        ((ProCGroups.OpenNormalSubgroup.comap
          (fundamentalGroupHom f xi).toMonoidHom
          (fundamentalGroupHom f xi).continuous_toFun U :
            OpenNormalSubgroup π₁ᵉᵗ(xi)) : Subgroup π₁ᵉᵗ(xi)) := by
    change (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
        (fundamentalGroupHom f xi).toMonoidHom =
      (U : Subgroup π₁ᵉᵗ(xi ≫ f)).comap
        (fundamentalGroupHom f xi).toMonoidHom
    exact congrArg
      (fun K : Subgroup π₁ᵉᵗ(xi ≫ f) ↦
        K.comap (fundamentalGroupHom f xi).toMonoidHom) hx
  let eSourceU := eSource.trans (subgroupContinuousMulEquivOfEq hSourceSub)
  let eTargetU := eTarget.trans (subgroupContinuousMulEquivOfEq hx)
  refine ⟨A, x, Z, i, z, hA, hZ, hi, eSourceU, eTargetU, ?_⟩
  intro a
  apply Subtype.ext
  let b := fundamentalGroupHom
    (i.left ≫ Limits.pullback.fst A.hom f)
    (fiberObjEquivHom xi Z z).left a
  have ha :
      ((eTarget b :
          MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x) : π₁ᵉᵗ(xi ≫ f)) =
        fundamentalGroupHom f xi
          ((eSource a :
            (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
              (fundamentalGroupHom f xi).toMonoidHom) : π₁ᵉᵗ(xi)) := by
    have ha' := congrArg Subtype.val (hcomm a)
    rw [restrictPreimage_coe] at ha'
    simpa only [b] using ha'
  have hTargetCoe :
      ((eTargetU b : U) : π₁ᵉᵗ(xi ≫ f)) =
        ((eTarget b : MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x) :
          π₁ᵉᵗ(xi ≫ f)) := by
    dsimp only [eTargetU, ContinuousMulEquiv.trans_apply]
    exact subgroupContinuousMulEquivOfEq_coe hx (eTarget b)
  have hSourceCoe :
      ((eSourceU a :
        ProCGroups.OpenNormalSubgroup.comap
          (fundamentalGroupHom f xi).toMonoidHom
          (fundamentalGroupHom f xi).continuous_toFun U) : π₁ᵉᵗ(xi)) =
        ((eSource a :
          (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
            (fundamentalGroupHom f xi).toMonoidHom) : π₁ᵉᵗ(xi)) := by
    dsimp only [eSourceU, ContinuousMulEquiv.trans_apply]
    exact subgroupContinuousMulEquivOfEq_coe hSourceSub (eSource a)
  change ((eTargetU b : U) : π₁ᵉᵗ(xi ≫ f)) =
    ((ProCGroups.ContinuousMonoidHom.restrictPreimage
      (fundamentalGroupHom f xi) (U : Subgroup π₁ᵉᵗ(xi ≫ f))
      (eSourceU a) : U) : π₁ᵉᵗ(xi ≫ f))
  calc
    ((eTargetU b : U) : π₁ᵉᵗ(xi ≫ f)) =
        ((eTarget b : MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x) :
          π₁ᵉᵗ(xi ≫ f)) := hTargetCoe
    _ = fundamentalGroupHom f xi
          ((eSource a :
            (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
              (fundamentalGroupHom f xi).toMonoidHom) : π₁ᵉᵗ(xi)) := ha
    _ = fundamentalGroupHom f xi
          ((eSourceU a : ProCGroups.OpenNormalSubgroup.comap
            (fundamentalGroupHom f xi).toMonoidHom
            (fundamentalGroupHom f xi).continuous_toFun U) : π₁ᵉᵗ(xi)) :=
      congrArg (fundamentalGroupHom f xi) hSourceCoe.symm
    _ = ((ProCGroups.ContinuousMonoidHom.restrictPreimage
          (fundamentalGroupHom f xi) (U : Subgroup π₁ᵉᵗ(xi ≫ f))
          (eSourceU a) : U) : π₁ᵉᵗ(xi ≫ f)) :=
      (restrictPreimage_coe _ _ _).symm

end AlgebraicGeometry.FiniteEtale
