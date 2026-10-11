/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.OpenImmersionExtensions
import EtaleFundamentalGroups.Purity.ConnectedNormalizationExtension

/-!
# Fundamental-group equivalence from canonical normalization extensions

For a quasi-compact open immersion, it suffices to prove that the canonical
function-field normalization attached to every connected Galois cover is
finite etale.  The normalization supplies the extension objects, and open
normal quotients then detect injectivity of the fundamental-group map.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Finite etaleness of every canonical Galois-cover normalization across a
nonempty quasi-compact open immersion identifies the two etale fundamental
groups. -/
noncomputable def fundamentalGroupEquivOfOpenImmersionCanonicalNormalizations
    {U X : Scheme.{u}}
    [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    [ConnectedSpace U]
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U]
    [QuasiCompact j] [QuasiSeparated j]
    (hEtale : ∀ (W : FiniteEtale U) (hW : IsGalois W),
      letI : IsGalois W := hW
      IsFiniteEtale
        (connectedCoverGenericComposite W ≫ j).fromNormalization)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U) :
    π₁ᵉᵗ(xi) ≃ₜ* π₁ᵉᵗ(xi ≫ j) := by
  apply fundamentalGroupEquivOfOpenImmersionGaloisExtensions j ?_ xi
  intro W hW
  letI : IsGalois W := hW
  exact connectedCoverExtensionOfNormalization W j (hEtale W hW)

@[simp]
theorem fundamentalGroupEquivOfOpenImmersionCanonicalNormalizations_apply
    {U X : Scheme.{u}}
    [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    [ConnectedSpace U]
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U]
    [QuasiCompact j] [QuasiSeparated j]
    (hEtale : ∀ (W : FiniteEtale U) (hW : IsGalois W),
      letI : IsGalois W := hW
      IsFiniteEtale
        (connectedCoverGenericComposite W ≫ j).fromNormalization)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U) (gamma : π₁ᵉᵗ(xi)) :
    fundamentalGroupEquivOfOpenImmersionCanonicalNormalizations
        j hEtale xi gamma =
      fundamentalGroupHom j xi gamma := by
  rfl

end AlgebraicGeometry.FiniteEtale

end
