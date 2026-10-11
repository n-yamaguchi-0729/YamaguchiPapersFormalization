/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.Basic
import EtaleCohomology.Constructible.OpenClosed
import EtaleCohomology.Constructible.Support
import EtaleCohomology.Sites.OpenAdjunction
import EtaleCohomology.Sites.ClosedAdjunction
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Constructible

/-!
# Constructibility of extension by zero and closed direct image

Zero extension along a quasi-compact open immersion preserves
constructibility. Closed direct image does so when the complementary open
image is retrocompact. Their composite treats locally closed immersions
presented by their open-closed factorization. All coefficient rings are
allowed and no noetherian hypothesis on the base scheme is imposed.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits
namespace EtaleCohomology
variable {X U Z : Scheme.{u}} {R : Type u} [CommRing R]

/-- Extension by zero along a quasi-compact open immersion preserves constructibility. -/
theorem IsEtaleConstructible.extensionByZero
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    {G : Sheaf U.smallEtaleTopology (ModuleCat.{u} R)} (hG : IsEtaleConstructible R G) :
    IsEtaleConstructible R ((etaleExtensionByZero j R).obj G) := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range j)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  have hi : Set.range I.subschemeι = (Set.range j)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hcompl : Set.range j = (Set.range I.subschemeι)ᶜ := by
    rw [hi, compl_compl]
  apply IsEtaleConstructible.of_open_closed j I.subschemeι hcompl
  · exact hG.of_iso (asIso ((etaleExtensionByZeroAdjunction j R).unit.app G))
  · apply IsEtaleFiniteTypeLocallyConstant.isEtaleConstructible
    apply isEtaleFiniteTypeLocallyConstant_of_isZero
    apply etalePullback_extensionByZero_isZero_of_disjoint I.subschemeι j _ G
    rw [hi]
    exact disjoint_compl_left

/-- Closed direct image preserves constructibility if the complementary open
image is retrocompact. This condition is automatic for noetherian bases. -/
theorem IsEtaleConstructible.closedPushforward
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : IsRetrocompact (Set.range i)ᶜ)
    {G : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)} (hG : IsEtaleConstructible R G) :
    IsEtaleConstructible R ((etalePushforward i R).obj G) := by
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : QuasiCompact U.ι :=
    quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hi)
  have hcompl : Set.range U.ι = (Set.range i)ᶜ := Scheme.Opens.range_ι U
  apply IsEtaleConstructible.of_open_closed U.ι i hcompl
  · apply IsEtaleFiniteTypeLocallyConstant.isEtaleConstructible
    apply isEtaleFiniteTypeLocallyConstant_of_isZero
    apply etalePullback_closedPushforward_isZero_of_disjoint U.ι i _ G
    rw [hcompl]
    exact disjoint_compl_left
  · have : IsIso ((etalePullbackPushforwardAdjunction i R).counit.app G) :=
      etalePushforwardClosed_counit_isIso i R G
    exact hG.of_iso (asIso ((etalePullbackPushforwardAdjunction i R).counit.app G)).symm

/-- Extension along an open-closed factorization of a locally closed immersion
preserves constructibility under the corresponding image conditions. -/
theorem IsEtaleConstructible.locallyClosedExtension
    (i : Z ⟶ U) [IsClosedImmersion i] (hi : IsRetrocompact (Set.range i)ᶜ)
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    {G : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)} (hG : IsEtaleConstructible R G) :
    IsEtaleConstructible R
      ((etaleExtensionByZero j R).obj ((etalePushforward i R).obj G)) :=
  (hG.closedPushforward i hi).extensionByZero j

end EtaleCohomology
