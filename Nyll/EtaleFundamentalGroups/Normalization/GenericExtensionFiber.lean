/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.GenericFiber
import Nyll.SchemeTheory.Normalization.FiniteSeparable

/-!
# Generic fibres of relative normalizations

The normalization of an integral scheme in an algebraic extension of its
function field recovers that extension on the generic fibre.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L]
  [Algebra X.functionField L]

private theorem genericExtensionSectionsIso_toSpec
    (U : X.Opens) [Nonempty U] :
    (X.genericExtensionMorphism L ⁻¹ᵁ U).ι ≫
        Spec.map (X.genericExtensionSectionsIso L U).hom =
      (X.genericExtensionMorphism L ⁻¹ᵁ U).toSpecΓ := by
  let V := X.genericExtensionMorphism L ⁻¹ᵁ U
  have hV : V = ⊤ := X.genericExtensionMorphism_preimage_eq_top L U
  change V.ι ≫ Spec.map ((Spec (.of L)).presheaf.mapIso
    (eqToIso hV.symm).op ≪≫ Scheme.ΓSpecIso (.of L)).hom = V.toSpecΓ
  have h : ∀ (W : (Spec (.of L)).Opens) (hW : W = ⊤),
      W.ι ≫ Spec.map ((Spec (.of L)).presheaf.mapIso
        (eqToIso hW.symm).op ≪≫ Scheme.ΓSpecIso (.of L)).hom = W.toSpecΓ := by
    intro W hW
    subst W
    simp only [eqToIso_refl, Iso.op_refl, Functor.mapIso_refl, Iso.refl_trans,
      SpecMap_ΓSpecIso_hom, Scheme.Opens.toSpecΓ_top]
  exact h V hV

/-- The affine chart of the normalization over `U`, expressed using the
literal integral closure inside `L`. -/
def genericNormalizationChart (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := X.affineExtensionAlgebra U L
    Spec (.of (integralClosure Γ(X, U) L)) ⟶
      (X.genericExtensionMorphism L).normalization := by
  letI := X.affineExtensionAlgebra U L
  letI := ((X.genericExtensionMorphism L).app U).hom.toAlgebra
  exact Spec.map (X.genericExtensionSectionsAlgEquiv L U).mapIntegralClosure.toCommRingCatIso.hom ≫
    (X.genericExtensionMorphism L).normalizationOpenCover.f ⟨U, hU⟩

/-- This chart has the original structure map from the integral closure. -/
@[reassoc]
theorem genericNormalizationChart_base
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := X.affineExtensionAlgebra U L
    genericNormalizationChart X L U hU ≫
        (X.genericExtensionMorphism L).fromNormalization =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L))) ≫
        hU.fromSpec := by
  let := X.affineExtensionAlgebra U L
  let := ((X.genericExtensionMorphism L).app U).hom.toAlgebra
  let c : Spec (.of (integralClosure Γ(X, U)
      Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ U))) ⟶
      (X.genericExtensionMorphism L).normalization :=
    (X.genericExtensionMorphism L).normalizationOpenCover.f ⟨U, hU⟩
  have hc : c ≫ (X.genericExtensionMorphism L).fromNormalization =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
        (integralClosure Γ(X, U) Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ U)))) ≫
        hU.fromSpec := (X.genericExtensionMorphism L).ι_fromNormalization ⟨U, hU⟩
  change (Spec.map (X.genericExtensionSectionsAlgEquiv L
    U).mapIntegralClosure.toCommRingCatIso.hom ≫
    c) ≫ _ = _
  rw [Category.assoc, hc, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (X.genericExtensionSectionsAlgEquiv L U).mapIntegralClosure.commutes r

/-- The inclusion of the integral closure into `L` gives the canonical map
into the relative normalization. -/
@[reassoc]
theorem spec_val_genericNormalizationChart
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := X.affineExtensionAlgebra U L
    Spec.map (CommRingCat.ofHom (algebraMap (integralClosure Γ(X, U) L) L)) ≫
        genericNormalizationChart X L U hU =
      (X.genericExtensionMorphism L).toNormalization := by
  let := X.affineExtensionAlgebra U L
  let := ((X.genericExtensionMorphism L).app U).hom.toAlgebra
  let V := X.genericExtensionMorphism L ⁻¹ᵁ U
  let c : Spec (.of (integralClosure Γ(X, U) Γ(Spec (.of L), V))) ⟶
      (X.genericExtensionMorphism L).normalization :=
    (X.genericExtensionMorphism L).normalizationOpenCover.f ⟨U, hU⟩
  let e := (X.genericExtensionSectionsAlgEquiv L U).mapIntegralClosure.toCommRingCatIso
  have hV : V = ⊤ := X.genericExtensionMorphism_preimage_eq_top L U
  let : IsIso V.ι := by
    have h : ∀ (W : (Spec (.of L)).Opens), W = ⊤ → IsIso W.ι := by
      intro W hW
      subst W
      exact inferInstanceAs (IsIso (Spec (.of L)).topIso.hom)
    exact h V hV
  let v : CommRingCat.of (integralClosure Γ(X, U) Γ(Spec (.of L), V)) ⟶
      Γ(Spec (.of L), V) :=
    CommRingCat.ofHom (R := integralClosure Γ(X, U) Γ(Spec (.of L), V))
      (S := Γ(Spec (.of L), V))
      (algebraMap (integralClosure Γ(X, U) Γ(Spec (.of L), V)) Γ(Spec (.of L), V))
  have hnorm : V.ι ≫ (X.genericExtensionMorphism L).toNormalization =
      V.toSpecΓ ≫ Spec.map v ≫ c :=
    (X.genericExtensionMorphism L).ι_toNormalization ⟨U, hU⟩
  have hval : e.hom ≫
      CommRingCat.ofHom (algebraMap (integralClosure Γ(X, U) L) L) =
      v ≫ (X.genericExtensionSectionsIso L U).hom := by
    ext x
    rfl
  apply (cancel_epi V.ι).mp
  change V.ι ≫ (Spec.map (CommRingCat.ofHom
    (algebraMap (integralClosure Γ(X, U) L) L)) ≫ Spec.map e.hom ≫ c) = _
  rw [hnorm, ← Spec.map_comp_assoc, hval, Spec.map_comp_assoc,
    ← Category.assoc, genericExtensionSectionsIso_toSpec]

/-- The integral-closure chart is the pullback of the affine open in `X`. -/
theorem isPullback_genericNormalizationChart
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := X.affineExtensionAlgebra U L
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L))))
      (genericNormalizationChart X L U hU) hU.fromSpec
      (X.genericExtensionMorphism L).fromNormalization := by
  let := X.affineExtensionAlgebra U L
  let := ((X.genericExtensionMorphism L).app U).hom.toAlgebra
  let c : Spec (.of (integralClosure Γ(X, U)
      Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ U))) ⟶
      (X.genericExtensionMorphism L).normalization :=
    (X.genericExtensionMorphism L).normalizationOpenCover.f ⟨U, hU⟩
  have hc : IsOpenImmersion c :=
    (X.genericExtensionMorphism L).normalizationOpenCover.map_prop ⟨U, hU⟩
  let : IsOpenImmersion c := hc
  let e := (X.genericExtensionSectionsAlgEquiv L U).mapIntegralClosure.toCommRingCatIso
  have he : IsIso (Spec.map e.hom) := inferInstance
  let : IsOpenImmersion (genericNormalizationChart X L U hU) :=
    inferInstanceAs (IsOpenImmersion (Spec.map e.hom ≫ c))
  apply IsOpenImmersion.isPullback
  · exact genericNormalizationChart_base X L U hU
  · rw [IsAffineOpen.opensRange_fromSpec]
    change (X.genericExtensionMorphism L).fromNormalization ⁻¹ᵁ U =
      (Spec.map e.hom ≫ c).opensRange
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    exact (X.genericExtensionMorphism L).fromNormalization_preimage ⟨U, hU⟩

/-- The generic fibre of the relative normalization in an algebraic
extension is that field extension, with its canonical normalization map. -/
theorem isPullback_genericExtensionNormalization
    [Algebra.IsAlgebraic X.functionField L] :
    IsPullback (X.genericExtensionMorphism L).toNormalization
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)))
      (X.genericExtensionMorphism L).fromNormalization
      (X.fromSpecStalk (genericPoint X)) := by
  obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := genericPoint X) (by trivial)
  let : Nonempty U := ⟨⟨genericPoint X, hηU⟩⟩
  let := X.affineExtensionAlgebra U L
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsScalarTower Γ(X, U) X.functionField L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have h := (isPullback_spec_integralClosure_generic Γ(X, U) X.functionField L).paste_horiz
    (isPullback_genericNormalizationChart X L U hU).flip
  rw [spec_val_genericNormalizationChart] at h
  have hg : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) X.functionField)) ≫
      hU.fromSpec = X.fromSpecStalk (genericPoint X) :=
    hU.fromSpecStalk_eq_fromSpecStalk hηU
  rw [hg] at h
  exact h

/-- The canonical comparison is an isomorphism from `Spec L` to the
generic pullback of the relative normalization. -/
def genericExtensionNormalizationFiberIso
    [Algebra.IsAlgebraic X.functionField L] :
    Spec (.of L) ≅ pullback (X.genericExtensionMorphism L).fromNormalization
      (X.fromSpecStalk (genericPoint X)) :=
  (isPullback_genericExtensionNormalization X L).isoPullback

@[reassoc]
theorem genericExtensionNormalizationFiberIso_hom_fst
    [Algebra.IsAlgebraic X.functionField L] :
    (genericExtensionNormalizationFiberIso X L).hom ≫ pullback.fst
        (X.genericExtensionMorphism L).fromNormalization (X.fromSpecStalk (genericPoint X)) =
      (X.genericExtensionMorphism L).toNormalization :=
  (isPullback_genericExtensionNormalization X L).isoPullback_hom_fst

@[reassoc]
theorem genericExtensionNormalizationFiberIso_hom_snd
    [Algebra.IsAlgebraic X.functionField L] :
    (genericExtensionNormalizationFiberIso X L).hom ≫ pullback.snd
        (X.genericExtensionMorphism L).fromNormalization (X.fromSpecStalk (genericPoint X)) =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) :=
  (isPullback_genericExtensionNormalization X L).isoPullback_hom_snd

end EtaleFundamentalGroups
