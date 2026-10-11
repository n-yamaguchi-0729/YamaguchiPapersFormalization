/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Morphisms.ClosedImmersion
import SchemeTheory.Morphisms.ClosedImmersionLift
import SchemeTheory.Morphisms.DominantBaseChange
import SchemeTheory.Morphisms.EtaleRadicial
import SchemeTheory.Morphisms.EtaleReduced
import SchemeTheory.Morphisms.Finite
import SchemeTheory.Morphisms.FiniteDescent
import SchemeTheory.Morphisms.Flat
import SchemeTheory.Morphisms.FlatRank
import SchemeTheory.Morphisms.GeometricallyIntegralDescent
import SchemeTheory.Morphisms.NormalizationFiniteFactor
import SchemeTheory.Morphisms.OpenImmersionLocalization
import SchemeTheory.Morphisms.OpenImmersionQuotient
import SchemeTheory.Morphisms.RadicialDescent
import SchemeTheory.Morphisms.Smooth
import SchemeTheory.Morphisms.SmoothLocus
import SchemeTheory.Morphisms.SigmaPullback
import SchemeTheory.Morphisms.UnramifiedHomExt
import SchemeTheory.Morphisms.SmoothGeometricallyIntegral
import SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed
import SchemeTheory.Morphisms.GeometricallyIntegralFieldDescent
import SchemeTheory.Morphisms.FiberRank
import SchemeTheory.Morphisms.QuasiFinite
import SchemeTheory.Morphisms.UnramifiedPointRigidity
import SchemeTheory.Morphisms.ResiduePointFixedness
import SchemeTheory.Morphisms.ProperNormalization
import SchemeTheory.Morphisms.FlatBaseChangeNormalization
import SchemeTheory.Morphisms.AffineNormalizationPushforward
import SchemeTheory.Morphisms.NormalizationPushforward
import SchemeTheory.Morphisms.NormalizationFlatBaseChangeIso
import SchemeTheory.Morphisms.EtalePostcomposition
import SchemeTheory.Morphisms.FiniteEtaleGeometricallyReduced
import SchemeTheory.Morphisms.ProperHenselianClosedRestriction
import SchemeTheory.Morphisms.ProperIntegralHenselianConnectedFiber
import SchemeTheory.Morphisms.ProperIntegralHenselianSections
import SchemeTheory.Morphisms.NoetherianProperFiberSections
import SchemeTheory.Morphisms.ChowDatumProj_nonempty_of
import SchemeTheory.Morphisms.ChowDatum_nonempty
import SchemeTheory.Morphisms.exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper
import SchemeTheory.Morphisms.ProperHenselianSheafRestriction

/-!
# Scheme morphisms

This facade collects the finite, flat, smooth, rank, reduced-etale, and
closed-immersion lemmas used by the finite étale and fundamental-group
developments.
-/

/- Canonical aggregate for SchemeTheory.Morphisms. -/
