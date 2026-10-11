/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryStrictLocalModel
import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryInertia
import Nyll.EtaleFundamentalGroups.Inertia.GeometricStalkNormalizationImage
import Mathlib.Algebra.Group.Subgroup.MulOpposite

/-!
# The strict-Henselian finite image lies in actual boundary inertia

At a boundary component use its canonical residue-field geometric point and
the actual geometric etale stalk. The shared point construction produces a
point of the original normalization over that very geometric point, fixed by
the entire finite image of the strict generic fundamental group.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia
open EtaleFundamentalGroups.StrictHenselian

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [IsLocallyNoetherian X]

/-- The actual strict-Henselian generic finite image is contained in the
stabilizer of a geometric point over the original component geometric point.
The point and the fixed action are constructed from the pointed cover. -/
theorem exists_componentNormalizationPoint_strictImage_le_inertia
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement] (E : Component D)
    {Ξ : Type} [Field Ξ] [IsSepClosed Ξ]
    (xi : Spec (.of Ξ) ⟶ Spec (.of (boundaryStrictFractionField D E)))
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (w : (FiniteEtale.fiber (xi ≫ boundaryStrictGenericMorphism D hreg E)).obj W) :
    ∃ z : Spec (.of (AlgebraicClosure (X.residueField (componentPoint D E)))) ⟶
        (W.hom ≫ D.1.supportComplement.ι).normalization,
      z ≫ (W.hom ≫ D.1.supportComplement.ι).fromNormalization = componentGeometricPoint D E ∧
      (finiteEtaleGaloisCoverQuotientOfMorphism
        (boundaryStrictGenericMorphism D hreg E) xi W hW w).range ≤
        (finiteCoverInertia D W E z).op := by
  let : IsDomain (X.presheaf.stalk (componentPoint D E)) :=
    isDomain_stalk_componentPoint D hreg E
  let : IsDiscreteValuationRing (X.presheaf.stalk (componentPoint D E)) :=
    isDiscreteValuationRing_stalk_componentPoint D hreg E
  obtain ⟨z, hz, hfixed⟩ :=
    exists_normalizationPoint_fixed_by_geometricStalk_finiteImage D (componentPoint D E)
      (boundaryComponentResidueMap D E) xi W hW w
  refine ⟨z, hz.trans ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom (boundaryComponentResidueMap D E)) ≫
      X.fromSpecStalk (componentPoint D E) =
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (componentPoint D E))
        (AlgebraicClosure (X.residueField (componentPoint D E))))) ≫
          X.fromSpecResidueField (componentPoint D E)
    rw [Scheme.fromSpecResidueField, ← Category.assoc, ← Spec.map_comp]
    rfl
  · intro σ hσ
    exact hfixed σ hσ

end Yamaguchi26SolvableCoverings
