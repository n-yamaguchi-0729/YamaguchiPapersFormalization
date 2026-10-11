/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleDatum
import SchemeTheory.RingTheory.Descent.FaithfullyFlatOnOpenImage
import SchemeTheory.RingTheory.Descent.FaithfullyFlatAlgebraEqualizer
import SchemeTheory.RingTheory.Descent.FaithfullyFlatGradedAlgebraEqualizer
import SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleEqualizer
import SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleHomDescent
import SchemeTheory.RingTheory.Descent.ModuleBaseChangeHomExt
import SchemeTheory.RingTheory.Descent.PrimeAwayAlgebraGluing
import SchemeTheory.RingTheory.Descent.PrimeAwayPairGluing
import SchemeTheory.RingTheory.Descent.PrimeAwayTensorDetection
import SchemeTheory.RingTheory.Descent.FiniteSubalgebraLocalization
import SchemeTheory.RingTheory.Descent.FiniteEtaleNeighborhood
import SchemeTheory.RingTheory.Descent.BoundaryNormalIntegralClosure
import SchemeTheory.RingTheory.Descent.IntegralClosureLocalizationAway
import SchemeTheory.RingTheory.Descent.FiniteNormalizationModel
import SchemeTheory.RingTheory.Descent.EtaleLocalNormality

import SchemeTheory.RingTheory.Descent.EtalePrimeLocalization
import SchemeTheory.RingTheory.Descent.FiniteNormalizationNeighborhood
import SchemeTheory.RingTheory.Descent.FiniteNormalizationSpreading

import SchemeTheory.RingTheory.Descent.FiniteType
import SchemeTheory.RingTheory.Descent.FinitePresentation
import SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import SchemeTheory.RingTheory.Descent.FaithfullyFlatNormality
import SchemeTheory.RingTheory.Descent.SmoothAtPrimeNormality

import SchemeTheory.RingTheory.Descent.InvertibleModule


/- Canonical aggregate for SchemeTheory.RingTheory.Descent. -/
import SchemeTheory.RingTheory.Descent.TensorComparison
import SchemeTheory.RingTheory.Descent.GradedSubalgebra
import SchemeTheory.RingTheory.Descent.GradedBaseChange
import SchemeTheory.RingTheory.Descent.EtaleSource
import SchemeTheory.RingTheory.Descent.EtaleOpenImage
import SchemeTheory.RingTheory.Descent.PrincipalLocalizationModel
import SchemeTheory.RingTheory.Descent.LocalizationNormalIntegralClosure
import SchemeTheory.RingTheory.Descent.FiniteUnramifiedNeighborhood
import SchemeTheory.RingTheory.Descent.EtaleLocalDomainOfIntegralNormalExtension
import SchemeTheory.RingTheory.Descent.EtaleLocalIrreducibilityOfIntegralNormalExtension

/-!
# Faithfully flat descent and gluing of algebras

This aggregate exposes module and algebra equalizers, homomorphism descent, prime-away
gluing, finite etale neighborhoods, and descent of finite type and finite presentation.
-/
