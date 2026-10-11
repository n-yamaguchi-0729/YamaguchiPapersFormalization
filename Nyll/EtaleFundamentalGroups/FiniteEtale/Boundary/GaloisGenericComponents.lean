/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticCondition
import Nyll.SchemeTheory.Divisors.IrreducibleComponentMap
import Nyll.EtaleFundamentalGroups.FiniteEtale.GaloisDomination
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Geometric generic boundary components in finite-etale towers

The geometric-integrality clause for boundary components after Galois
finite-etale covers is inherited after a connected Galois pullback.  The
proof dominates a composite cover by a Galois cover of the original base
and descends geometric integrality along a finite surjective morphism of
reduced irreducible components.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry

universe u

namespace Scheme.EffectiveCartierDivisor

variable {X S : Scheme.{u}}

/-- Geometric integrality of a boundary component descends from a Galois
cover dominating the given finite-etale cover. -/
lemma geometricallyIntegral_component_of_galois_domination
    [IsIntegral X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.HasGeometricallyIntegralGenericComponentsAfterGaloisCovers p)
    (W A : FiniteEtale X) [ConnectedSpace W.left]
    (a : A ⟶ W) (hA : IsGalois A)
    (F : Set (D.1.comap W.hom).subscheme)
    (hF : F ∈ irreducibleComponents (D.1.comap W.hom).subscheme) :
    GeometricallyIntegral
      (((D.1.comap W.hom).componentToBase (W.hom ≫ p) F hF).fiberToSpecResidueField
        (genericPoint S)) := by
  let : ConnectedSpace A.left := by
    let : IsGalois A := hA
    exact FiniteEtale.connectedSpace_left_of_isConnected A
  let af : A.left ⟶ W.left := a.hom.left
  let : Surjective af := IsFiniteEtale.surjective af
  let I : W.left.IdealSheafData := D.1.comap W.hom
  let g : (I.comap af).subscheme ⟶ I.subscheme :=
    I.comapSubschemeTo af
  let : Surjective g := by
    let : Surjective (pullback.snd af I.subschemeι) :=
      inferInstance
    dsimp only [g, I, IdealSheafData.comapSubschemeTo]
    infer_instance
  obtain ⟨E, hE, himage⟩ :=
    TopologicalSpace.exists_irreducibleComponent_image_eq_of_surjective
      g.continuous g.isClosedMap (Flat.generalizingMap g) g.surjective F hF
  let e := (I.comap af).subscheme.reducedIrreducibleComponentMap
    g E hE F hF himage
  let : IsFinite e := inferInstance
  let : Surjective e := inferInstance
  have hDA0 := hD A hA
  have haw : af ≫ W.hom = A.hom := a.hom.w
  dsimp only [pulledBackComponentToBase] at hDA0
  rw [← haw] at hDA0
  have hcomp : D.1.comap (af ≫ W.hom) = I.comap af := by
    simpa only [I] using D.1.comap_comp af W.hom
  have hDA1 := hcomp ▸ hDA0
  have hDA : ∀ (E : Set (I.comap af).subscheme)
      (hE : E ∈ irreducibleComponents (I.comap af).subscheme),
      GeometricallyIntegral
        (((I.comap af).componentToBase
          ((af ≫ W.hom) ≫ p) E hE).fiberToSpecResidueField
            (genericPoint S)) := by
    exact hDA1
  have hEgi := hDA E hE
  have hebase :
      e ≫ I.componentToBase (W.hom ≫ p) F hF =
        (I.comap af).componentToBase
          ((af ≫ W.hom) ≫ p) E hE := by
    dsimp only [e, IdealSheafData.componentToBase]
    rw [Scheme.reducedIrreducibleComponentMap_ι_assoc]
    dsimp only [g]
    rw [IdealSheafData.comapSubschemeTo_subschemeι_assoc]
    simp only [Category.assoc]
  apply GeometricallyIntegral.genericFiber_of_comp_of_isDominant
    e (I.componentToBase (W.hom ≫ p) F hF)
  rw [hebase]
  exact hEgi

/-- In a two-stage connected finite-etale tower, geometric integrality of
every generic boundary component follows from the Galois-cover clause on the
original base. -/
lemma geometricallyIntegralGenericComponents_after_galois_tower
    [IsIntegral X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.HasGeometricallyIntegralGenericComponentsAfterGaloisCovers p)
    (Y : FiniteEtale X) [ConnectedSpace Y.left]
    (Zc : FiniteEtale Y.left) (hZc : IsGalois Zc)
    (F : Set ((D.1.comap Y.hom).comap Zc.hom).subscheme)
    (hF : F ∈ irreducibleComponents
      ((D.1.comap Y.hom).comap Zc.hom).subscheme) :
    GeometricallyIntegral
      ((((D.1.comap Y.hom).comap Zc.hom).componentToBase
        ((Zc.hom ≫ Y.hom) ≫ p) F hF).fiberToSpecResidueField
          (genericPoint S)) := by
  let : ConnectedSpace Zc.left := by
    let : IsGalois Zc := hZc
    exact FiniteEtale.connectedSpace_left_of_isConnected Zc
  let hcomp : IsFiniteEtale (Zc.hom ≫ Y.hom) :=
    MorphismProperty.comp_mem @IsFiniteEtale Zc.hom Y.hom Zc.prop Y.prop
  let W : FiniteEtale X :=
    @FiniteEtale.mk _ _ (Zc.hom ≫ Y.hom) hcomp
  let : ConnectedSpace W.left := by
    change ConnectedSpace Zc.left
    infer_instance
  obtain ⟨A, a, hA⟩ := FiniteEtale.exists_galois_domination W
  have hAll : ∀ (F : Set (D.1.comap W.hom).subscheme)
      (hF : F ∈ irreducibleComponents (D.1.comap W.hom).subscheme),
      GeometricallyIntegral
        (((D.1.comap W.hom).componentToBase
          (W.hom ≫ p) F hF).fiberToSpecResidueField (genericPoint S)) := by
    intro F hF
    exact geometricallyIntegral_component_of_galois_domination
      D p hD W A a hA F hF
  have hcomap : D.1.comap W.hom = (D.1.comap Y.hom).comap Zc.hom := by
    change D.1.comap (Zc.hom ≫ Y.hom) =
      (D.1.comap Y.hom).comap Zc.hom
    exact D.1.comap_comp Zc.hom Y.hom
  have hAll' := hcomap ▸ hAll
  exact hAll' F hF

private theorem connectedSpaceLeftOfIsGalois [ConnectedSpace X]
    (Y : FiniteEtale X) (hY : IsGalois Y) : ConnectedSpace Y.left := by
  let : IsGalois Y := hY
  exact FiniteEtale.connectedSpace_left_of_isConnected Y

/-- The geometric-integrality clause on all connected Galois covers is
inherited by a connected finite-etale Galois pullback. -/
lemma geometricallyIntegralGenericComponents_after_galoisPullback
    [IsIntegral X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.HasGeometricallyIntegralGenericComponentsAfterGaloisCovers p)
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    letI : ConnectedSpace Y.left := connectedSpaceLeftOfIsGalois Y hY
    ∀ (Zc : FiniteEtale Y.left), IsGalois Zc →
      ∀ (F : Set ((D.1.comap Y.hom).comap Zc.hom).subscheme)
        (hF : F ∈ irreducibleComponents
          ((D.1.comap Y.hom).comap Zc.hom).subscheme),
        GeometricallyIntegral
          ((((D.1.comap Y.hom).comap Zc.hom).componentToBase
            ((Zc.hom ≫ Y.hom) ≫ p) F hF).fiberToSpecResidueField
              (genericPoint S)) :=
  @geometricallyIntegralGenericComponents_after_galois_tower
    X S _ _ D p hD Y (connectedSpaceLeftOfIsGalois Y hY)

end Scheme.EffectiveCartierDivisor

end AlgebraicGeometry
