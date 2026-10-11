/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryStalkNormalizationEtale
import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryExtension
import Nyll.EtaleFundamentalGroups.Purity.CartierNormalizationSpreading
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationExtension

/-!
# Extending covers with trivial boundary stabilizers

Purity supplies finite etaleness over every boundary stalk. Affine spreading
then makes the actual relative normalization finite etale globally. Its
restriction is the original cover, so the finite-cover kernel criterion
supplies the remaining inclusion in the boundary quotient formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [IsLocallyNoetherian X]

/-- A Galois cover whose normalization is etale at every component stalk extends across the
regular Cartier boundary as the actual relative normalization. -/
theorem exists_finiteEtale_extension_of_componentStalks
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hgeneric : ∀ E : Component D,
      Etale (CategoryTheory.Limits.pullback.snd
        (W.hom ≫ D.1.supportComplement.ι).fromNormalization
        (X.fromSpecStalk (componentPoint D E)))) :
    ∃ V : FiniteEtale X,
      Nonempty ((FiniteEtale.pullback D.1.supportComplement.ι).obj V ≅ W) := by
  have hfinite : IsFiniteEtale (W.hom ≫ D.1.supportComplement.ι).fromNormalization :=
    finiteEtale_normalization_of_cartier_boundary_stalks D hreg W
      (normalization_boundaryStalk_finiteEtale_of_componentStalks D hreg W hW hgeneric)
  exact Inertia.exists_finiteEtale_extension_of_normalization D.1.supportComplement W

/-- A Galois cover with trivial boundary stabilizers extends across the
regular Cartier boundary as the actual relative normalization. -/
theorem exists_finiteEtale_extension_of_boundaryUnramified
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hU : IsBoundaryUnramified D W) :
    ∃ V : FiniteEtale X,
      Nonempty ((FiniteEtale.pullback D.1.supportComplement.ι).obj V ≅ W) := by
  exact exists_finiteEtale_extension_of_componentStalks D hreg W hW
    (boundaryUnramified_normalization_componentStalk_etale D hreg W hW hU)

/-- Every element killed by the ambient fundamental-group map is killed
by each Galois quotient with trivial boundary stabilizers. -/
theorem kernel_le_boundaryUnramifiedKernelIntersection
    [ConnectedSpace X]
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ D.1.supportComplement) :
    (fundamentalGroupHom D.1.supportComplement.ι point).toMonoidHom.ker ≤
      boundaryUnramifiedKernelIntersection D point := by
  rw [fundamentalGroupHom_ker_eq_iInf_extendableGalois D.1.supportComplement.ι point
    (boundaryComplement_fundamentalGroupHom_surjective D hreg point)]
  intro g hg
  simp only [boundaryUnramifiedKernelIntersection, Subgroup.mem_iInf] at hg ⊢
  intro W hW w hU
  exact hg W hW w (exists_finiteEtale_extension_of_boundaryUnramified D hreg W hW hU)

end Yamaguchi26SolvableCoverings
