/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.StrictHenselianNormalizationImage
import Nyll.EtaleFundamentalGroups.StrictHenselian.CartierGenericPoint
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The actual geometric-stalk image fixes a normalization point

The local model is the constructed geometric etale stalk, its generic map is
the actual Cartier-complement factorization, and its closed point is the
evaluation into the originally specified algebraically closed field. These
suppliers instantiate the strict-local image theorem without any further
point or action-comparison assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The finite image of the fraction field of the actual geometric stalk
fixes a geometric point of the original normalization over the same closed
geometric point. -/
theorem exists_normalizationPoint_fixed_by_geometricStalk_finiteImage
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) [ConnectedSpace D.1.supportComplement]
    (x : X) [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (φ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ]
    {Ξ : Type u} [Field Ξ] [IsSepClosed Ξ] :
    let S := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let j := geometricStalkFractionFieldToComplement D x φ
    ∀ (xi : Spec (.of Ξ) ⟶ Spec (.of (FractionRing S)))
      (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
      (w : (FiniteEtale.fiber (xi ≫ j)).obj W),
    ∃ z : Spec (.of Ω) ⟶ (W.hom ≫ D.1.supportComplement.ι).normalization,
      z ≫ (W.hom ≫ D.1.supportComplement.ι).fromNormalization =
        Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x ∧
      ∀ σ : (Aut W)ᵐᵒᵖ,
        σ ∈ (finiteEtaleGaloisCoverQuotientOfMorphism j xi W hW w).range →
        z ≫ normalizationEndomorphism (W.hom ≫ D.1.supportComplement.ι) σ.unop.hom.left
          (by
            rw [← Category.assoc]
            exact congrArg (fun k => k ≫ D.1.supportComplement.ι) σ.unop.hom.w) = z := by
  intro S j xi W hW w
  let b : Spec (.of S) ⟶ X :=
    Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) ≫ X.fromSpecStalk x
  have hjb : j ≫ D.1.supportComplement.ι =
      Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S))) ≫ b := by
    exact (geometricStalkFractionFieldToComplement_comp_ι D x φ).trans
      ((congrArg (fun k => k ≫ X.fromSpecStalk x)
        (Spec.map_comp (CommRingCat.ofHom (geometricStalkStructureMap φ))
          (CommRingCat.ofHom (algebraMap S (FractionRing S))))).trans
        (Category.assoc _ _ _))
  let ψ : S →+* Ω := (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom
  obtain ⟨z, hz, hfixed⟩ :=
    exists_normalizationPoint_fixed_by_strictHenselian_finiteImage S (FractionRing S)
      D.1.supportComplement.ι b j hjb ψ xi W hW w
  refine ⟨z, hz.trans ?_, hfixed⟩
  change Spec.map (CommRingCat.ofHom ψ) ≫
    (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) ≫ X.fromSpecStalk x) = _
  rw [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun k => Spec.map (CommRingCat.ofHom k) ≫ X.fromSpecStalk x)
    (geometricStalkStructureMap_evaluation φ)

end EtaleFundamentalGroups.Inertia
