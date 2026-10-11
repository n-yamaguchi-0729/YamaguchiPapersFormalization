/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.Normalization.Affine
import SchemeTheory.Normalization.CompositumEmbedding
import SchemeTheory.Normalization.ConductorQuotient
import SchemeTheory.Normalization.FiniteEtaleOpen
import SchemeTheory.Normalization.FiniteSeparable
import SchemeTheory.Normalization.GenericFiber.All
import SchemeTheory.Normalization.HenselianIntegralSection
import SchemeTheory.Normalization.HenselianSectionFactor
import SchemeTheory.Normalization.IntegralClosure.All
import SchemeTheory.Normalization.IntegralOpen
import SchemeTheory.Normalization.Localization.All
import SchemeTheory.Normalization.Normal
import SchemeTheory.Normalization.PrimeSeparation
import SchemeTheory.Normalization.Products.All
import SchemeTheory.Normalization.QuotientFiniteFactor

import SchemeTheory.Normalization.AffineFiniteEtale




/- Canonical aggregate for SchemeTheory.Normalization. -/
import SchemeTheory.Normalization.NativeNormalizationPrime
import SchemeTheory.Normalization.IntegralClosureAutomorphisms
import SchemeTheory.Normalization.NormalizationAutomorphismSurjectivity
import SchemeTheory.Normalization.NormalizationGaloisSurjectivity
import SchemeTheory.Normalization.IntegralClosureAutomorphismRestriction
import SchemeTheory.Normalization.NormalizationAutomorphismGroupMap
import SchemeTheory.Normalization.ScalarRestrictionGroupMap
import SchemeTheory.Normalization.NativeAutomorphismRingMaps
import SchemeTheory.Normalization.AmbientNormalizationGroupMap
import SchemeTheory.Normalization.NativeNormalizationRingMap
import SchemeTheory.Normalization.SubalgebraNormalizationTower
import SchemeTheory.Normalization.SubalgebraNormalizationTowerRamification
import SchemeTheory.Normalization.FiniteNormalSource

/-!
# Normalization of affine curves

This facade collects normalization finiteness, conductor-quotient, and
prime-separation results.
-/
