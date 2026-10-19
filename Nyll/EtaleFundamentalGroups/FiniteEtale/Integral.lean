/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.Connected
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.SchemeTheory.Normalization.FiniteSeparable

/-!
# Integral connected finite-etale covers

This file passes from the generic-component calculation for finite-etale
algebras to connected finite-etale covers of normal integral schemes.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

private theorem irreducibleSpace_of_connectedSpace_of_irreducible_openCover
    {A I : Type*} [TopologicalSpace A] [ConnectedSpace A]
    (U : I → TopologicalSpace.Opens A)
    (hcover : (⨆ i, U i) = ⊤)
    (hU : ∀ i, IrreducibleSpace (U i)) : IrreducibleSpace A := by
  classical
  let r (i j : I) : Prop :=
    ((U i : Set A) ∩ (U j : Set A)).Nonempty
  have hstep {O : Set A} (hO : IsOpen O) {i j : I} (hij : r i j) :
      (O ∩ (U i : Set A)).Nonempty →
        (O ∩ (U j : Set A)).Nonempty := by
    intro hOi
    let : IrreducibleSpace (U i) := hU i
    have hi : IsPreirreducible (U i : Set A) :=
      IsPreirreducible.of_subtype
    obtain ⟨x, hxi, hxO, hxj⟩ :=
      hi O (U j : Set A) hO (U j).isOpen
        (by simpa [Set.inter_comm] using hOi) hij
    exact ⟨x, hxO, hxj⟩
  have hpropagate {O : Set A} (hO : IsOpen O) {i j : I}
      (hij : Relation.EqvGen r i j) :
      (O ∩ (U i : Set A)).Nonempty ↔
        (O ∩ (U j : Set A)).Nonempty := by
    induction hij with
    | rel i j hij =>
        have hji : r j i := by
          obtain ⟨x, hxi, hxj⟩ := hij
          exact ⟨x, hxj, hxi⟩
        exact ⟨hstep hO hij, hstep hO hji⟩
    | refl i => exact Iff.rfl
    | symm i j _ ih => exact ih.symm
    | trans i j k _ _ hij hjk => exact hij.trans hjk
  obtain ⟨a₀⟩ := (inferInstance : Nonempty A)
  have ha₀ : ∃ i, a₀ ∈ U i := by
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [hcover]
    trivial
  let i₀ : I := Classical.choose ha₀
  let C : Set A :=
    ⋃ (j : I) (_ : Relation.EqvGen r i₀ j), (U j : Set A)
  have hCopen : IsOpen C := by
    dsimp only [C]
    exact isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ (U j).isOpen
  have hCnonempty : C.Nonempty := by
    let : IrreducibleSpace (U i₀) := hU i₀
    obtain ⟨x⟩ := (inferInstance : Nonempty (U i₀))
    exact ⟨x.1, Set.mem_iUnion_of_mem i₀ <|
      Set.mem_iUnion_of_mem (Relation.EqvGen.refl i₀) x.2⟩
  have hCcomplOpen : IsOpen Cᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hxC
    have hxcover : ∃ j, x ∈ U j := by
      apply TopologicalSpace.Opens.mem_iSup.mp
      rw [hcover]
      trivial
    obtain ⟨j, hxj⟩ := hxcover
    refine Filter.mem_of_superset ((U j).isOpen.mem_nhds hxj) ?_
    intro y hyj hyC
    simp only [Set.mem_compl_iff] at hxC
    simp only [C, Set.mem_iUnion] at hyC
    obtain ⟨k, hk, hyk⟩ := hyC
    have hjk : r j k := by
      change ((U j : Set A) ∩ (U k : Set A)).Nonempty
      exact ⟨y, hyj, hyk⟩
    have hi₀j : Relation.EqvGen r i₀ j :=
      Relation.EqvGen.trans i₀ k j hk
        (Relation.EqvGen.symm j k (Relation.EqvGen.rel j k hjk))
    apply hxC
    exact Set.mem_iUnion_of_mem j <| Set.mem_iUnion_of_mem hi₀j hxj
  have hC : C = Set.univ :=
    IsClopen.eq_univ ⟨isOpen_compl_iff.mp hCcomplOpen, hCopen⟩ hCnonempty
  have hconnected (i : I) : Relation.EqvGen r i₀ i := by
    let : IrreducibleSpace (U i) := hU i
    obtain ⟨x⟩ := (inferInstance : Nonempty (U i))
    have hxC : x.1 ∈ C := by rw [hC]; trivial
    simp only [C, Set.mem_iUnion] at hxC
    obtain ⟨j, hj, hxj⟩ := hxC
    have hji : r j i := by
      change ((U j : Set A) ∩ (U i : Set A)).Nonempty
      exact ⟨x.1, hxj, x.2⟩
    exact Relation.EqvGen.trans i₀ j i hj
      (Relation.EqvGen.rel j i hji)
  rw [irreducibleSpace_def]
  refine ⟨Set.univ_nonempty, ?_⟩
  intro O V hO hV hOnonempty hVnonempty
  obtain ⟨x, hxO⟩ := hOnonempty
  obtain ⟨y, hyV⟩ := hVnonempty
  have hxcover : ∃ i, x ∈ U i := by
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [hcover]
    trivial
  have hycover : ∃ j, y ∈ U j := by
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [hcover]
    trivial
  obtain ⟨i, hxi⟩ := hxcover
  obtain ⟨j, hyj⟩ := hycover
  have hij : Relation.EqvGen r i j :=
    Relation.EqvGen.trans i i₀ j
      (Relation.EqvGen.symm i₀ i (hconnected i)) (hconnected j)
  have hOj : (O ∩ (U j : Set A)).Nonempty :=
    (hpropagate hO hij).mp ⟨x, hxO.2, hxi⟩
  let : IrreducibleSpace (U j) := hU j
  have hj : IsPreirreducible (U j : Set A) :=
    IsPreirreducible.of_subtype
  obtain ⟨z, -, hzO, hzV⟩ :=
    hj O V hO hV (by simpa [Set.inter_comm] using hOj)
      ⟨y, hyj, hyV.2⟩
  exact ⟨z, Set.mem_univ z, hzO, hzV⟩

/-- Over an affine normal integral base, a finite-etale cover with connected
source is integral. -/
theorem isIntegral_of_isFiniteEtale_of_isAffine_of_connectedSpace
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFiniteEtale f]
    [IsIntegral X] [IsNormalIntegral X] [IsAffine X]
    [ConnectedSpace Y] : IsIntegral Y := by
  let R := Γ(X, ⊤)
  let T := Γ(Y, ⊤)
  let K := X.functionField
  let : IsAffine Y := isAffine_of_isAffineHom f
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩
  let : Algebra R T := f.appTop.hom.toAlgebra
  let : Module.Finite R T := by
    rw [← RingHom.finite_algebraMap]
    exact f.finite_appTop
  have hfEtale : f.appTop.hom.Etale := by
    rw [← HasRingHomProperty.iff_of_isAffine
      (P := @AlgebraicGeometry.Etale)]
    infer_instance
  let : Algebra.Etale R T := hfEtale.toAlgebra
  let : IsIntegrallyClosed R :=
    IsNormalIntegral.affine_isIntegrallyClosed ⊤ (isAffineOpen_top X)
  let : Algebra R K := X.affineExtensionAlgebra ⊤ K
  let : IsFractionRing R K :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  let : ConnectedSpace (PrimeSpectrum T) := by
    change ConnectedSpace (Spec (.of T))
    exact Y.isoSpec.hom.homeomorph.connectedSpace_iff.mp inferInstance
  let : IsDomain T :=
    finiteEtale_isDomain_of_connectedSpace_primeSpectrum
      (R := R) (T := T) (K := K)
  exact isIntegral_of_isAffine_of_isDomain Y

/-- A connected component of the source of a finite-etale morphism over an
affine normal integral scheme is integral. -/
theorem isIntegral_connectedComponent_of_isFiniteEtale_of_isAffine
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFiniteEtale f]
    [IsIntegral X] [IsNormalIntegral X] [IsAffine X]
    [Finite (_root_.ConnectedComponents Y)]
    (i : _root_.ConnectedComponents Y) :
    IsIntegral (Y.connectedComponents.X i) := by
  let c : Y.connectedComponents.X i ⟶ Y :=
    Y.connectedComponents.f i
  let g : Y.connectedComponents.X i ⟶ X := c ≫ f
  let : IsOpenImmersion c := by
    dsimp only [c, Scheme.connectedComponents]
    infer_instance
  let : IsClosedImmersion c := by
    dsimp only [c]
    infer_instance
  let hc : IsFiniteEtale c :=
    { toIsFinite := inferInstance
      toEtale := inferInstance }
  let hg : IsFiniteEtale g := by
    dsimp only [g]
    exact MorphismProperty.comp_mem @IsFiniteEtale c f hc inferInstance
  let : IsFiniteEtale g := hg
  exact isIntegral_of_isFiniteEtale_of_isAffine_of_connectedSpace g

/-- A categorically connected finite-etale cover of a normal integral scheme
has integral source.  No finite-type or arithmetic-base hypothesis is used. -/
theorem isIntegral_left_of_isConnected_finiteEtale
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] : IsIntegral Y.left := by
  classical
  let : ConnectedSpace Y.left :=
    AlgebraicGeometry.FiniteEtale.connectedSpace_left_of_isConnected Y
  have hAffine (y : Y.left) :
      ∃ U : X.Opens, IsAffineOpen U ∧ Y.hom.base y ∈ U ∧ U ≤ ⊤ :=
    exists_isAffineOpen_mem_and_subset
      (X := X) (U := ⊤) (x := Y.hom.base y) trivial
  let U (y : Y.left) : X.Opens := Classical.choose (hAffine y)
  have hrestrEtale (y : Y.left) : IsFiniteEtale (Y.hom ∣_ U y) := by
    exact MorphismProperty.of_isPullback
      (isPullback_morphismRestrict Y.hom (U y)).flip Y.2
  have hUaffine (y : Y.left) : IsAffineOpen (U y) :=
    (Classical.choose_spec (hAffine y)).1
  have hyU (y : Y.left) : Y.hom.base y ∈ U y :=
    (Classical.choose_spec (hAffine y)).2.1
  have hUnonempty (y : Y.left) : Nonempty (U y) :=
    ⟨⟨Y.hom.base y, hyU y⟩⟩
  let V (y : Y.left) : Y.left.Opens := Y.hom ⁻¹ᵁ U y
  have hyV (y : Y.left) : y ∈ V y := hyU y
  have hfiniteComponents (y : Y.left) :
      Finite (_root_.ConnectedComponents (V y)) := by
    let : Nonempty (U y) := hUnonempty y
    let : IsAffine (U y) := hUaffine y
    let A : FiniteEtale (U y) :=
      @FiniteEtale.mk _ _ (Y.hom ∣_ U y) (hrestrEtale y)
    change Finite (_root_.ConnectedComponents A.left)
    infer_instance
  let i (y : Y.left) : _root_.ConnectedComponents (V y) :=
    _root_.ConnectedComponents.mk ⟨y, hyV y⟩
  let C (y : Y.left) : (V y : Scheme).OpenCover :=
    letI : Finite (_root_.ConnectedComponents (V y)) :=
      hfiniteComponents y
    (V y : Scheme).connectedComponents
  let Z (y : Y.left) : Scheme.{u} :=
    (C y).X (i y)
  let c (y : Y.left) : Z y ⟶ V y :=
    (C y).f (i y)
  have hcOpen (y : Y.left) : IsOpenImmersion (c y) := by
    let : Finite (_root_.ConnectedComponents (V y)) :=
      hfiniteComponents y
    dsimp only [c, C, Scheme.connectedComponents]
    exact (Scheme.connCompOpen (X := (V y : Scheme)) (i y)).instIsOpenImmersionι
  let j (y : Y.left) : Z y ⟶ Y.left := c y ≫ (V y).ι
  have hjOpen (y : Y.left) : IsOpenImmersion (j y) := by
    dsimp only [j]
    exact MorphismProperty.comp_mem @IsOpenImmersion
      (c y) (V y).ι (hcOpen y) inferInstance
  let W (y : Y.left) : Y.left.Opens :=
    (j y).opensRange (H := hjOpen y)
  have hZintegral (y : Y.left) : IsIntegral (Z y) := by
    let : Nonempty (U y) := hUnonempty y
    let : IsAffine (U y) := hUaffine y
    let hUint : IsIntegral (U y) :=
      isIntegral_of_isOpenImmersion (U y).ι
    let : IsIntegral (U y) := hUint
    let hUnormal : IsNormalIntegral (U y) := inferInstance
    let : Finite (_root_.ConnectedComponents (V y)) :=
      hfiniteComponents y
    change IsIntegral ((V y : Scheme).connectedComponents.X (i y))
    exact @isIntegral_connectedComponent_of_isFiniteEtale_of_isAffine
      (U y) (V y) (Y.hom ∣_ U y) (hrestrEtale y) hUint hUnormal
      (hUaffine y) (hfiniteComponents y) (i y)
  have hWintegral (y : Y.left) : IsIntegral (W y) := by
    let : IsIntegral (Z y) := hZintegral y
    have : IsOpenImmersion (j y) := hjOpen y
    let e : Z y ≅ W y :=
      IsOpenImmersion.isoOfRangeEq (j y) (W y).ι <| by
        rw [Scheme.Opens.range_ι]
        exact (Scheme.Hom.coe_opensRange (j y)).symm
    exact IsIntegral.of_isIso e.hom
  have hWcover : (⨆ y, W y) = ⊤ := by
    apply top_unique
    intro y _
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨y, ?_⟩
    have : Finite (_root_.ConnectedComponents (V y)) :=
      hfiniteComponents y
    let v : V y := ⟨y, hyV y⟩
    let z : Z y := by
      dsimp only [Z]
      refine ⟨v, ?_⟩
      change _root_.ConnectedComponents.mk v ∈
        ({i y} : Set (_root_.ConnectedComponents (V y)))
      exact Set.mem_singleton _
    let : IsOpenImmersion (j y) := hjOpen y
    change y ∈ (j y).opensRange
    exact Scheme.Hom.mem_opensRange.mpr ⟨z, rfl⟩
  let : IrreducibleSpace Y.left :=
    irreducibleSpace_of_connectedSpace_of_irreducible_openCover
      W hWcover (fun y ↦ by
        let : IsIntegral (W y) := hWintegral y
        exact irreducibleSpace_of_isIntegral (W y))
  let : IsReduced Y.left := by
    have hstalk (y : Y.left) : _root_.IsReduced (Y.left.presheaf.stalk y) := by
      have hyW : ∃ z, y ∈ W z := by
        apply TopologicalSpace.Opens.mem_iSup.mp
        rw [hWcover]
        trivial
      obtain ⟨z, hyz⟩ := hyW
      let : IsIntegral (W z) := hWintegral z
      let w : (W z : Scheme) := ⟨y, hyz⟩
      let e : Y.left.presheaf.stalk y ≃+* (W z : Scheme).presheaf.stalk w :=
        (asIso ((W z).ι.stalkMap w)).commRingCatIsoToRingEquiv
      exact isReduced_of_injective e.toRingHom e.injective
    exact isReduced_of_isReduced_stalk Y.left
  exact isIntegral_of_irreducibleSpace_of_isReduced Y.left

/-- The source of a finite-etale cover of a locally Noetherian scheme is
locally Noetherian. -/
theorem isLocallyNoetherian_left_finiteEtale
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Y : FiniteEtale X) : IsLocallyNoetherian Y.left :=
  @LocallyOfFiniteType.isLocallyNoetherian Y.left X Y.hom
    (((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType Y.hom).mp
      Y.prop.toIsFinite).2)
    (inferInstance : IsLocallyNoetherian X)

/-- A categorically connected finite-etale cover of a normal integral
scheme has normal integral source. -/
theorem isNormalIntegral_left_of_isConnected_finiteEtale
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    IsNormalIntegral Y.left := by
  classical
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  apply IsNormalIntegral.of_stalks Y.left
  intro y
  have hAffine :
      ∃ U : X.Opens, IsAffineOpen U ∧ Y.hom.base y ∈ U ∧ U ≤ ⊤ :=
    exists_isAffineOpen_mem_and_subset
      (X := X) (U := ⊤) (x := Y.hom.base y) trivial
  let U : X.Opens := Classical.choose hAffine
  have hUaffine : IsAffineOpen U :=
    (Classical.choose_spec hAffine).1
  have hyU : Y.hom.base y ∈ U :=
    (Classical.choose_spec hAffine).2.1
  have hUnonempty : Nonempty U := ⟨⟨Y.hom.base y, hyU⟩⟩
  let V : Y.left.Opens := Y.hom ⁻¹ᵁ U
  have hyV : y ∈ V := hyU
  have hrestrEtale : IsFiniteEtale (Y.hom ∣_ U) := by
    exact MorphismProperty.of_isPullback
      (isPullback_morphismRestrict Y.hom U).flip Y.2
  have hfiniteComponents :
      Finite (_root_.ConnectedComponents V) := by
    let : Nonempty U := hUnonempty
    let : IsAffine U := hUaffine
    let A : FiniteEtale U :=
      @FiniteEtale.mk _ _ (Y.hom ∣_ U) hrestrEtale
    change Finite (_root_.ConnectedComponents A.left)
    infer_instance
  let v : V := ⟨y, hyV⟩
  let i : _root_.ConnectedComponents V :=
    _root_.ConnectedComponents.mk v
  let C : (V : Scheme).OpenCover :=
    letI : Finite (_root_.ConnectedComponents V) := hfiniteComponents
    (V : Scheme).connectedComponents
  let Z : Scheme.{u} := C.X i
  let c : Z ⟶ V := C.f i
  have hcOpen : IsOpenImmersion c := by
    let : Finite (_root_.ConnectedComponents V) := hfiniteComponents
    dsimp only [c, C, Scheme.connectedComponents]
    exact (Scheme.connCompOpen (X := (V : Scheme)) i).instIsOpenImmersionι
  have hcClosed : IsClosedImmersion c := by
    dsimp only [c]
    infer_instance
  let g : Z ⟶ U := c ≫ (Y.hom ∣_ U)
  have hcFiniteEtale : IsFiniteEtale c :=
    { toIsFinite := inferInstance
      toEtale := inferInstance }
  have hgFiniteEtale : IsFiniteEtale g := by
    dsimp only [g]
    exact MorphismProperty.comp_mem @IsFiniteEtale
      c (Y.hom ∣_ U) hcFiniteEtale hrestrEtale
  have hZintegral : IsIntegral Z := by
    let : Nonempty U := hUnonempty
    let : IsAffine U := hUaffine
    let hUint : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
    let : IsIntegral U := hUint
    let hUnormal : IsNormalIntegral U := inferInstance
    let : Finite (_root_.ConnectedComponents V) := hfiniteComponents
    change IsIntegral ((V : Scheme).connectedComponents.X i)
    exact @isIntegral_connectedComponent_of_isFiniteEtale_of_isAffine
      U V (Y.hom ∣_ U) hrestrEtale hUint hUnormal hUaffine
      hfiniteComponents i
  have hZnormal : @IsNormalIntegral Z hZintegral := by
    let : Nonempty U := hUnonempty
    let : IsAffine U := hUaffine
    let : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
    let : IsNormalIntegral U := inferInstance
    let : IsIntegral Z := hZintegral
    let : IsFiniteEtale g := hgFiniteEtale
    let : IsAffine Z := isAffine_of_isAffineHom g
    let R := Γ(U, ⊤)
    let T := Γ(Z, ⊤)
    let K := (U : Scheme).functionField
    let : Nonempty (⊤ : (U : Scheme).Opens) :=
      ⟨⟨Classical.choice hUnonempty, trivial⟩⟩
    let : Algebra R T := g.appTop.hom.toAlgebra
    let : Module.Finite R T := by
      rw [← RingHom.finite_algebraMap]
      exact g.finite_appTop
    have hgEtale : g.appTop.hom.Etale := by
      rw [← HasRingHomProperty.iff_of_isAffine
        (P := @AlgebraicGeometry.Etale)]
      infer_instance
    let : Algebra.Etale R T := hgEtale.toAlgebra
    let : IsIntegrallyClosed R :=
      IsNormalIntegral.affine_isIntegrallyClosed ⊤ (isAffineOpen_top U)
    let : Algebra R K := (U : Scheme).affineExtensionAlgebra ⊤ K
    let : IsFractionRing R K :=
      functionField_isFractionRing_of_isAffineOpen (U : Scheme) ⊤
        (isAffineOpen_top (U : Scheme))
    let : ConnectedSpace (PrimeSpectrum T) := by
      change ConnectedSpace (Spec (.of T))
      exact Z.isoSpec.hom.homeomorph.connectedSpace_iff.mp inferInstance
    let : IsIntegrallyClosed T :=
      finiteEtale_isIntegrallyClosed_of_connectedSpace_primeSpectrum
        (R := R) (T := T) (K := K)
    exact IsNormalIntegral.of_isAffine Z
  let j : Z ⟶ Y.left := c ≫ V.ι
  have hjOpen : IsOpenImmersion j := by
    dsimp only [j]
    exact MorphismProperty.comp_mem @IsOpenImmersion
      c V.ι hcOpen inferInstance
  let z : Z := by
    dsimp only [Z, C]
    refine ⟨v, ?_⟩
    change _root_.ConnectedComponents.mk v ∈
      ({i} : Set (_root_.ConnectedComponents V))
    exact Set.mem_singleton _
  let : IsIntegral Z := hZintegral
  let : IsNormalIntegral Z := hZnormal
  let : IsOpenImmersion j := hjOpen
  have hzNormal : IsIntegrallyClosed (Z.presheaf.stalk z) :=
    IsNormalIntegral.stalk_isIntegrallyClosed z
  let e : Z.presheaf.stalk z ≃+* Y.left.presheaf.stalk (j z) :=
    (asIso (j.stalkMap z)).symm.commRingCatIsoToRingEquiv
  have hjz : j z = y := rfl
  have htarget :=
    (@IsIntegrallyClosed.of_equiv
      (Z.presheaf.stalk z) (Y.left.presheaf.stalk (j z))
      _ _ e hzNormal)
  rw [hjz] at htarget
  exact htarget

/-- Pullback along a nonempty open immersion preserves categorical
connectedness for finite-etale covers of a normal integral
scheme. -/
theorem pullback_obj_isConnected_of_isOpenImmersion
    {X U : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U]
    (Y : FiniteEtale X) [IsConnected Y] :
    IsConnected ((FiniteEtale.pullback j).obj Y) := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : ConnectedSpace X := inferInstance
  let : ConnectedSpace U := inferInstance
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let P : FiniteEtale U := (FiniteEtale.pullback j).obj Y
  let : Nonempty P.left :=
    FiniteEtale.pullback_obj_nonempty j Y
  let iP : P.left ⟶ Y.left :=
    pullback.fst Y.hom j
  have hiP : IsOpenImmersion iP := by
    dsimp only [iP]
    exact MorphismProperty.pullback_fst Y.hom j
      (show IsOpenImmersion j from inferInstance)
  let : IsOpenImmersion iP := hiP
  let : IsIntegral P.left := by
    exact isIntegral_of_isOpenImmersion iP
  let : ConnectedSpace P.left := inferInstance
  exact FiniteEtale.isConnected_of_connectedSpace_left P

end EtaleFundamentalGroups
