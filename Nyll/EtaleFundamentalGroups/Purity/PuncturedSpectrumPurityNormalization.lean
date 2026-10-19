/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.OpenImmersion
import Nyll.EtaleFundamentalGroups.Purity.ConnectedNormalizationExtension
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Canonical normalization under punctured purity

This file compares the canonical function-field normalization attached to a
connected punctured cover with an arbitrary finite-etale extension of that
cover.  Consequently, categorical punctured purity makes the canonical
normalization itself finite etale.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

private theorem eqToHom_stalk_eq_stalkCongr
    (Z : Scheme.{u}) {z z' : Z} (h : z = z') :
    eqToHom (congrArg (fun w ↦ Z.presheaf.stalk w) h) =
      (Z.presheaf.stalkCongr (.of_eq h)).hom := by
  subst z'
  exact (Z.presheaf.stalkSpecializes_refl z).symm

/-- The generic-point morphism is natural for a dense morphism of integral
schemes and the induced literal map on function fields. -/
theorem genericExtensionMorphism_functionFieldMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : DenseRange f) :
    Spec.map (CommRingCat.ofHom (f.functionFieldMap hf)) ≫
        X.genericExtensionMorphism X.functionField =
      Y.genericExtensionMorphism Y.functionField ≫ f := by
  let h : f (genericPoint Y) = genericPoint X :=
    f.map_genericPoint_of_denseRange hf
  unfold Scheme.genericExtensionMorphism
  rw [show CommRingCat.ofHom
      (algebraMap X.functionField X.functionField) = 𝟙 _ by rfl]
  rw [show CommRingCat.ofHom
      (algebraMap Y.functionField Y.functionField) = 𝟙 _ by rfl]
  rw [Spec.map_id, Spec.map_id, Category.id_comp, Category.id_comp]
  unfold Scheme.Hom.functionFieldMap
  rw [show CommRingCat.ofHom
      (CommRingCat.Hom.hom
        (eqToHom _ ≫ f.stalkMap (genericPoint Y))) =
      eqToHom _ ≫ f.stalkMap (genericPoint Y) by rfl]
  rw [Spec.map_comp]
  simp only [Category.assoc]
  rw [eqToHom_stalk_eq_stalkCongr]
  all_goals try exact h.symm
  rw [TopCat.Presheaf.stalkCongr_hom]
  exact (congrArg (fun k => Spec.map (f.stalkMap (genericPoint Y)) ≫ k)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (specializes_of_eq h))).trans
      (Scheme.SpecMap_stalkMap_fromSpecStalk f (x := genericPoint Y))

/-- Relative normalization is unchanged when the source of the defining
morphism is replaced by an isomorphic scheme. -/
noncomputable def normalizationSourceIso
    {Y Y' X : Scheme.{u}} (e : Y ≅ Y') (f : Y' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] :
    (e.hom ≫ f).normalization ≅ f.normalization := by
  let g : Y ⟶ X := e.hom ≫ f
  let a : g.normalization ⟶ f.normalization :=
    g.normalizationDesc (e.hom ≫ f.toNormalization)
      f.fromNormalization (by simp [g])
  let b : f.normalization ⟶ g.normalization :=
    f.normalizationDesc (e.inv ≫ g.toNormalization)
      g.fromNormalization (by simp [g])
  refine ⟨a, b, ?_, ?_⟩
  · apply Scheme.Hom.normalization.hom_ext g
      (a ≫ b) (𝟙 _) g.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · exact Category.id_comp _
  · apply Scheme.Hom.normalization.hom_ext f
      (b ≫ a) (𝟙 _) f.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · exact Category.id_comp _

@[reassoc (attr := simp)]
theorem normalizationSourceIso_hom_fromNormalization
    {Y Y' X : Scheme.{u}} (e : Y ≅ Y') (f : Y' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] :
    (normalizationSourceIso e f).hom ≫ f.fromNormalization =
      (e.hom ≫ f).fromNormalization := by
  simp [normalizationSourceIso]

/-- Equality-compatible form of `normalizationSourceIso`. -/
noncomputable def normalizationSourceIsoOfEq
    {Y Y' X : Scheme.{u}} (e : Y ≅ Y') (f : Y' ⟶ X)
    (g : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (h : e.hom ≫ f = g) :
    g.normalization ≅ f.normalization := by
  subst g
  exact normalizationSourceIso e f

@[reassoc (attr := simp)]
theorem normalizationSourceIsoOfEq_hom_fromNormalization
    {Y Y' X : Scheme.{u}} (e : Y ≅ Y') (f : Y' ⟶ X)
    (g : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (h : e.hom ≫ f = g) :
    (normalizationSourceIsoOfEq e f g h).hom ≫
        f.fromNormalization = g.fromNormalization := by
  subst g
  exact normalizationSourceIso_hom_fromNormalization e f

/-- Pullback along a quasi-compact open immersion into an integral scheme
reflects connectedness of finite-etale covers. -/
theorem isConnected_of_pullback_isConnected_of_isOpenImmersion
    {X U : Scheme.{u}} [IsIntegral X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [Nonempty U]
    (Z : FiniteEtale X)
    (hP : IsConnected ((pullback j).obj Z)) : IsConnected Z := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let P : FiniteEtale U := (pullback j).obj Z
  let : IsConnected P := hP
  let : ConnectedSpace P.left :=
    connectedSpace_left_of_isConnected P
  let hjDense : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  let : IsDominant j := ⟨hjDense⟩
  let hstd : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.of_isDominant j
  let hjqc : QuasiCompact j := inferInstance
  let iP : P.left ⟶ Z.left := pullback.fst Z.hom j
  let hflat : Flat Z.hom :=
    Etale.iff_flat_and_formallyUnramified.mp Z.prop.toEtale |>.1
  let : IsSchemeTheoreticallyDominant iP := by
    dsimp only [iP]
    exact @IsSchemeTheoreticallyDominant.pullbackFst _ _ _
      Z.hom j hstd hjqc hflat
  let : QuasiCompact iP := by
    dsimp only [iP]
    have hbase : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{u})
        (fun {_ _} f => QuasiCompact f) := quasiCompact_isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} f => QuasiCompact f)
      (IsPullback.of_hasPullback Z.hom j).flip hjqc
  let : PreconnectedSpace Z.left :=
    iP.denseRange.preconnectedSpace iP.continuous
  let : ConnectedSpace Z.left :=
    { toNonempty := Nonempty.map iP (inferInstance : Nonempty P.left) }
  exact FiniteEtale.isConnected_of_connectedSpace_left Z

/-- Connectedness of a finite-etale cover is transported against an
isomorphism. -/
theorem isConnected_of_iso_to_isConnected
    {X : Scheme.{u}} [ConnectedSpace X]
    (Z W : FiniteEtale X) (e : Z ≅ W) [IsConnected W] : IsConnected Z := by
  let heHom : IsIso e.hom.hom := (FiniteEtale.forget X).map_isIso e.hom
  let heLeft : IsIso e.hom.left :=
    @Functor.map_isIso _ _ _ _ _ _ (Over.forget X) e.hom.hom heHom
  let : ConnectedSpace Z.left :=
    (@asIso _ _ _ _ e.hom.left heLeft).hom.homeomorph.connectedSpace_iff.mpr
      (connectedSpace_left_of_isConnected W)
  exact isConnected_of_connectedSpace_left Z

/-- A morphism obtained from the generic composite of a connected
finite-etale cover by replacing its source with an isomorphic scheme has
finite-etale relative normalization. -/
theorem normalization_isFiniteEtale_of_sourceIso_connectedCover
    {X Y : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (Z : FiniteEtale X) [IsConnected Z] [IsIntegral Z.left]
    (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (eSource : Y ≅ Spec (.of Z.left.functionField))
    (hSource : eSource.hom ≫ connectedCoverGenericComposite Z = f) :
    IsFiniteEtale f.fromNormalization := by
  let fZ : Spec (.of Z.left.functionField) ⟶ X :=
    connectedCoverGenericComposite Z
  let eNormalization : f.normalization ≅ fZ.normalization :=
    normalizationSourceIsoOfEq eSource fZ f hSource
  let eZ : fZ.normalization ≅ Z.left :=
    connectedCoverGenericNormalizationIso Z
  let eTotal : f.normalization ≅ Z.left := eNormalization ≪≫ eZ
  have hNormalization :
      eNormalization.hom ≫ fZ.fromNormalization = f.fromNormalization :=
    normalizationSourceIsoOfEq_hom_fromNormalization
      eSource fZ f hSource
  have hInv : eZ.inv ≫ fZ.fromNormalization = Z.hom := by
    dsimp only [eZ, fZ]
    exact connectedCoverGenericNormalizationIso_inv_fromNormalization Z
  have hZ : eZ.hom ≫ Z.hom = fZ.fromNormalization := by
    calc
      eZ.hom ≫ Z.hom =
          eZ.hom ≫ (eZ.inv ≫ fZ.fromNormalization) := by
        exact congrArg (fun k ↦ eZ.hom ≫ k) hInv.symm
      _ = fZ.fromNormalization := Iso.hom_inv_id_assoc _ _
  have hTotal : eTotal.hom ≫ Z.hom = f.fromNormalization := by
    calc
      eTotal.hom ≫ Z.hom =
          eNormalization.hom ≫ (eZ.hom ≫ Z.hom) := by
        change (eNormalization.hom ≫ eZ.hom) ≫ Z.hom = _
        exact Category.assoc _ _ _
      _ = eNormalization.hom ≫ fZ.fromNormalization := by
        exact congrArg (fun k ↦ eNormalization.hom ≫ k) hZ
      _ = f.fromNormalization := hNormalization
  have hFiniteEtale : IsFiniteEtale (eTotal.hom ≫ Z.hom) := by
    let : IsFiniteEtale Z.hom := Z.prop
    let : IsFiniteEtale eTotal.hom := by constructor
    infer_instance
  rw [hTotal] at hFiniteEtale
  exact hFiniteEtale

/-- If a connected finite-etale cover of a dense open subscheme has some
finite-etale extension, then its canonical function-field normalization is
itself finite etale. -/
theorem connectedCoverGenericNormalization_isFiniteEtale_of_extension
    {X U : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j]
    (W : FiniteEtale U) [IsConnected W]
    (Z : FiniteEtale X) (e : (pullback j).obj Z ≅ W) :
    IsFiniteEtale
      (connectedCoverGenericComposite W ≫ j).fromNormalization := by
  let P : FiniteEtale U := (pullback j).obj Z
  let pHom : P.left ⟶ U := P.hom
  let wHom : W.left ⟶ U := W.hom
  let zHom : Z.left ⟶ X := Z.hom
  let : IsConnected P := isConnected_of_iso_to_isConnected P W e
  let : IsConnected Z :=
    isConnected_of_pullback_isConnected_of_isOpenImmersion j Z inferInstance
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : IsIntegral Z.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Z
  let iP : P.left ⟶ Z.left := pullback.fst Z.hom j
  let : IsOpenImmersion iP := by
    dsimp only [iP]
    exact MorphismProperty.pullback_fst (P := @IsOpenImmersion)
      Z.hom j (show IsOpenImmersion j from inferInstance)
  let heInvHom : IsIso e.inv.hom :=
    (FiniteEtale.forget U).map_isIso e.inv
  let heInvLeft : IsIso e.inv.left :=
    @Functor.map_isIso _ _ _ _ _ _ (Over.forget U) e.inv.hom heInvHom
  let g : W.left ⟶ Z.left := e.inv.left ≫ iP
  let : IsOpenImmersion g := by
    dsimp only [g]
    exact MorphismProperty.comp_mem @IsOpenImmersion
      e.inv.left iP inferInstance inferInstance
  let hg : DenseRange g :=
    g.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace g
  let q : CommRingCat.of Z.left.functionField ⟶
      CommRingCat.of W.left.functionField :=
    CommRingCat.ofHom (g.functionFieldMap hg)
  have hqBijective : Function.Bijective q := by
    change Function.Bijective (g.functionFieldMap hg)
    simpa only using g.functionFieldMap_bijective_of_isOpenImmersion
  let : IsIso q :=
    (ConcreteCategory.isIso_iff_bijective q).mpr hqBijective
  let eSource : Spec (.of W.left.functionField) ≅
      Spec (.of Z.left.functionField) := asIso (Spec.map q)
  have hgeneric :
      eSource.hom ≫ connectedCoverGenericMorphism Z =
        connectedCoverGenericMorphism W ≫ g := by
    dsimp only [eSource, q, asIso_hom, connectedCoverGenericMorphism]
    exact genericExtensionMorphism_functionFieldMap g hg
  have hP_hom : pHom = pullback.snd Z.hom j := by
    dsimp only [pHom, P, FiniteEtale.pullback]
    rfl
  have hebase : e.inv.left ≫ pHom = wHom := by
    dsimp only [pHom, wHom, P]
    exact e.inv.hom.w
  have hiPbase : iP ≫ zHom = pHom ≫ j := by
    dsimp only [zHom, iP]
    have hcondition : pullback.fst Z.hom j ≫ Z.hom =
        pullback.snd Z.hom j ≫ j := pullback.condition
    have hhomcomp : pHom ≫ j = pullback.snd Z.hom j ≫ j :=
      congrArg (fun k ↦ k ≫ j) hP_hom
    exact hcondition.trans hhomcomp.symm
  have hgbase : g ≫ zHom = wHom ≫ j := by
    dsimp only [g]
    rw [Category.assoc, hiPbase, ← Category.assoc, hebase]
  let fZ : Spec (.of Z.left.functionField) ⟶ X :=
    connectedCoverGenericComposite Z
  let fW : Spec (.of W.left.functionField) ⟶ X :=
    connectedCoverGenericComposite W ≫ j
  have hSource : eSource.hom ≫ fZ = fW := by
    change eSource.hom ≫ (connectedCoverGenericMorphism Z ≫ zHom) =
      (connectedCoverGenericMorphism W ≫ wHom) ≫ j
    rw [← Category.assoc, hgeneric, Category.assoc, hgbase,
      ← Category.assoc]
  exact normalization_isFiniteEtale_of_sourceIso_connectedCover
    Z fW eSource hSource

/-- Under punctured purity, the canonical function-field normalization of a
connected punctured cover is finite etale. -/
theorem connectedPuncturedCoverGenericNormalization_isFiniteEtale_of_hasPuncturedPurity
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegral (Scheme.puncturedSpectrum R)]
    (hpurity : HasPuncturedPurity R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    IsFiniteEtale
      (connectedCoverGenericComposite W ≫
        Scheme.puncturedSpectrumInclusion R).fromNormalization := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  obtain ⟨Z, ⟨e⟩⟩ := (hasPuncturedPurity_iff R).mp hpurity W
  exact connectedCoverGenericNormalization_isFiniteEtale_of_extension
    j W Z e

end AlgebraicGeometry.FiniteEtale

end
