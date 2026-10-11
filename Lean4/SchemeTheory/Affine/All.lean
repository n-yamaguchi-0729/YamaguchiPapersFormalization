/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Affine.SeparatedIntersections
import SchemeTheory.Affine.PullbackSectionsPushout
import SchemeTheory.Affine.FlatBaseChangeSections
import SchemeTheory.Affine.FlatMinimalPrime
import SchemeTheory.Affine.GeometricPointLocalization
import SchemeTheory.Affine.GeometricIrreducibility
import SchemeTheory.Affine.Over
import SchemeTheory.Affine.Property
import SchemeTheory.Affine.RegularSection
import SchemeTheory.Affine.StalkLocalization
import SchemeTheory.Affine.WeilRestriction.All
import SchemeTheory.Affine.PrimePairHartogs
import SchemeTheory.Affine.FlatBaseChangeAffinization
import SchemeTheory.Affine.AffinizationDescent

import SchemeTheory.Affine.ChartStalkLocalization

import SchemeTheory.Affine.StalkBaseChange
import SchemeTheory.Affine.SpecSectionMap
import SchemeTheory.Affine.HomeomorphismIdempotentSections
import SchemeTheory.Affine.ConnectedOfGlobalSections
import SchemeTheory.Affine.GeometricallyConnectedOfGlobalSections
import SchemeTheory.Affine.FaithfullyFlatSectionSurjectivity
import SchemeTheory.Affine.SpecFlatBaseChangeSections
import SchemeTheory.Affine.SurjectiveSectionPushout
import SchemeTheory.Affine.StalkBaseChangeSections
/-!
# Affine scheme infrastructure

This facade collects affine-over-base colimits, affine morphism properties,
flat minimal-prime control, and geometric irreducibility of affine schemes.
-/

/- Canonical aggregate for SchemeTheory.Affine. -/
