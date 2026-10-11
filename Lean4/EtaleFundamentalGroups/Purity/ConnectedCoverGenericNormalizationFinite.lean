/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.PuncturedSpectrumPurityNormalization

/-!
# Finiteness of canonical normalizations from dense open covers

A connected finite-etale cover of a nonempty quasi-compact open subscheme
induces a finite separable extension of the ambient function field.  Hence
the relative normalization of the ambient scheme in that extension is
finite.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry

universe u

private theorem eqToHom_stalk_eq_stalkCongr
    (Z : Scheme.{u}) {z z' : Z} (h : z = z') :
    eqToHom (congrArg (fun w ↦ Z.presheaf.stalk w) h) =
      (Z.presheaf.stalkCongr (.of_eq h)).hom := by
  subst z'
  simp

private theorem functionFieldMap_comp_of_denseRange
    {T S R : Scheme.{u}} [IsIntegral T] [IsIntegral S] [IsIntegral R]
    (f : S ⟶ T) (hf : DenseRange f)
    (g : R ⟶ S) (hg : DenseRange g) :
    let hgf : DenseRange (g ≫ f) := by
      change DenseRange (f.base ∘ g.base)
      exact hf.comp hg f.continuous
    (g.functionFieldMap hg).comp (f.functionFieldMap hf) =
      (g ≫ f).functionFieldMap hgf := by
  let hgf : DenseRange (g ≫ f) := by
    change DenseRange (f.base ∘ g.base)
    exact hf.comp hg f.continuous
  change (g.functionFieldMap hg).comp (f.functionFieldMap hf) =
    (g ≫ f).functionFieldMap hgf
  let hfgeneric : f (genericPoint S) = genericPoint T :=
    f.map_genericPoint_of_denseRange hf
  let hggeneric : g (genericPoint R) = genericPoint S :=
    g.map_genericPoint_of_denseRange hg
  let hgfgeneric : (g ≫ f) (genericPoint R) = genericPoint T :=
    (g ≫ f).map_genericPoint_of_denseRange hgf
  unfold Scheme.Hom.functionFieldMap
  rw [eqToHom_stalk_eq_stalkCongr T hfgeneric.symm,
    eqToHom_stalk_eq_stalkCongr S hggeneric.symm,
    eqToHom_stalk_eq_stalkCongr T hgfgeneric.symm]
  rw [← CommRingCat.hom_comp]
  rw [Category.assoc]
  rw [Scheme.Hom.stalkMap_congr_point_assoc f
      (genericPoint S) (g (genericPoint R)) hggeneric.symm]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  have hstalk := TopCat.Presheaf.stalkSpecializes_comp_assoc T.presheaf
    (specializes_of_eq (congrArg (fun z : S => f z) hggeneric))
    (specializes_of_eq hfgeneric)
    (f.stalkMap (g (genericPoint R)) ≫ g.stalkMap (genericPoint R))
  exact congrArg CommRingCat.Hom.hom
    (hstalk.trans (congrArg
      (fun k : T.presheaf.stalk (f (g (genericPoint R))) ⟶
          R.presheaf.stalk (genericPoint R) =>
        T.presheaf.stalkSpecializes (specializes_of_eq hgfgeneric) ≫ k)
      (Scheme.Hom.stalkMap_comp g f (genericPoint R)).symm))

namespace IsNormalIntegral

/-- The source of a nonempty open immersion into a normal integral scheme
is normal. -/
theorem of_isOpenImmersion
    {X U : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsIntegral U] (j : U ⟶ X) [IsOpenImmersion j] :
    IsNormalIntegral U := by
  let e : U ≅ j.opensRange := j.isoOpensRange
  let : Nonempty j.opensRange := Nonempty.map e.hom inferInstance
  apply IsNormalIntegral.of_stalks U
  intro u
  let : IsIntegrallyClosed
      ((j.opensRange : Scheme).presheaf.stalk (e.hom u)) :=
    IsNormalIntegral.stalk_isIntegrallyClosed (e.hom u)
  exact IsIntegrallyClosed.of_equiv
    (asIso (e.hom.stalkMap u)).commRingCatIsoToRingEquiv

end IsNormalIntegral

namespace FiniteEtale

private theorem isFinite_fromNormalization_of_eq
    {Y X : Scheme.{u}} (f g : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    (h : f = g) (hf : IsFinite f.fromNormalization) :
    IsFinite g.fromNormalization := by
  subst g
  exact hf

/-- The generic composite attached to a connected finite-etale cover of an
open subscheme is the generic-extension morphism for the induced ambient
function-field algebra structure. -/
theorem genericExtensionMorphism_eq_connectedCoverGenericComposite_comp
    {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
    [IsNormalIntegral U] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j]
    (W : FiniteEtale U) [IsConnected W] :
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let L := W.left.functionField
    letI : Algebra U.functionField L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    let e : X.functionField ≃+* U.functionField :=
      j.functionFieldRingEquivOfIsOpenImmersion
    letI : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp e.toRingHom).toAlgebra
    X.genericExtensionMorphism L = connectedCoverGenericComposite W ≫ j := by
  dsimp only
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L := W.left.functionField
  let : Algebra U.functionField L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let e : X.functionField ≃+* U.functionField :=
    j.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra X.functionField L :=
    ((algebraMap U.functionField L).comp e.toRingHom).toAlgebra
  let hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  let wHom : W.left ⟶ U := W.hom
  let hw : DenseRange wHom :=
    EtaleFundamentalGroups.finiteEtale_hom_denseRange_of_isConnected W
  let q : W.left ⟶ X := wHom ≫ j
  let hq : DenseRange q := by
    change DenseRange (j.base ∘ wHom.base)
    exact hj.comp hw j.continuous
  have hfieldMap :
      algebraMap X.functionField L = q.functionFieldMap hq := by
    have hcomp := functionFieldMap_comp_of_denseRange j hj wHom hw
    change
      (wHom.functionFieldMap hw).comp (j.functionFieldMap hj) =
        q.functionFieldMap hq
    exact hcomp.trans (by rfl)
  have hnatural := genericExtensionMorphism_functionFieldMap q hq
  rw [← hfieldMap] at hnatural
  have hXself :
      CommRingCat.ofHom
          (algebraMap X.functionField X.functionField) = 𝟙 _ := rfl
  have hLself :
      CommRingCat.ofHom (algebraMap L L) = 𝟙 _ := rfl
  simpa only [Scheme.genericExtensionMorphism, q,
    connectedCoverGenericComposite, connectedCoverGenericMorphism,
    wHom, hXself, hLself, Spec.map_id, Category.id_comp,
    Category.comp_id, Category.assoc] using hnatural

private theorem connectedCoverGenericNormalization_isFinite_core
    {X U : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (W : FiniteEtale U) [IsConnected W] :
    IsFinite (connectedCoverGenericComposite W ≫ j).fromNormalization := by
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L := W.left.functionField
  let : Algebra U.functionField L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let e : X.functionField ≃+* U.functionField :=
    j.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra X.functionField L :=
    ((algebraMap U.functionField L).comp e.toRingHom).toAlgebra
  have hcompat :
      (algebraMap X.functionField L).comp e.symm.toRingHom =
        (RingEquiv.refl L).toRingHom.comp (algebraMap U.functionField L) := by
    ext a
    simp [RingHom.algebraMap_toAlgebra]
  let : FiniteDimensional U.functionField L :=
    EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : FiniteDimensional X.functionField L :=
    Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl L) hcompat
  let : Algebra.IsSeparable U.functionField L :=
    EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable X.functionField L :=
    Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl L) hcompat
  have hsource :
      X.genericExtensionMorphism L = connectedCoverGenericComposite W ≫ j := by
    exact genericExtensionMorphism_eq_connectedCoverGenericComposite_comp j W
  exact isFinite_fromNormalization_of_eq
    (X.genericExtensionMorphism L)
    (connectedCoverGenericComposite W ≫ j) hsource
    (Scheme.Hom.isFinite_fromNormalization_genericExtension X L)

/-- The canonical relative normalization attached to a connected
finite-etale cover of a nonempty quasi-compact open subscheme is finite over
the ambient normal locally Noetherian integral scheme. -/
theorem connectedCoverGenericNormalization_isFinite_of_isOpenImmersion
    {X U : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    [Nonempty U]
    (W : FiniteEtale U) [IsConnected W] :
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    letI : IsNormalIntegral U := IsNormalIntegral.of_isOpenImmersion j
    letI : IsLocallyNoetherian U :=
      isLocallyNoetherian_of_isOpenImmersion j
    IsFinite (connectedCoverGenericComposite W ≫ j).fromNormalization := by
  let hUintegral : IsIntegral U := isIntegral_of_isOpenImmersion j
  let hUnormal : @IsNormalIntegral U hUintegral :=
    @IsNormalIntegral.of_isOpenImmersion X U _ _ hUintegral j _
  let hUnoetherian : IsLocallyNoetherian U :=
    isLocallyNoetherian_of_isOpenImmersion j
  exact @connectedCoverGenericNormalization_isFinite_core
    X U _ _ _
      hUintegral hUnormal hUnoetherian
    j _ _ _ W _

end FiniteEtale

end AlgebraicGeometry

end
