/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Theorem1Dot1AbFaithfulness
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem1Dot2PrimeOrderTest
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem1Dot3SigmaProperties
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem2Dot1ElementarySplitCriterion
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem3Dot1PrimePowerRoots
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem3Dot3FiniteOrderModP
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem3Dot4PrincipalUnitLogarithm
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem3Dot5CompletePrimeDegree
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem3Dot6MixedCharacteristic
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem4Dot1ResidueZeroLift
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem4Dot2HigherLocalFields
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem5Dot1FaithfulAbelianExtension
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem5Dot2AbelianSplitSolvableSlim
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot1FormalHilbert90
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot2IntegralInvariants
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot3CentralizerCriterion
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot4RelativeCriterion
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot5GroupCriterion
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot6AbsoluteCenter
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot7FieldSlimExamples
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.All
import Nyll.Yamaguchi26AbfaithfulGalois.HigherLocalField.All
import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.All
import Nyll.Yamaguchi26AbfaithfulGalois.FieldExamples.All
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.All
import Nyll.Yamaguchi26AbfaithfulGalois.Analytic.All

/-!
# Ab-faithfulness of absolute Galois groups

Formalization of Naganori Yamaguchi's [Ab-faithfulness of absolute Galois groups in number
theory](https://arxiv.org/abs/2610.05634v1), using the numbering of arXiv v1. Covers solvable
extensions, cohomological criteria, slimness and field examples. Example 2.2, Lemma 6.8 and the
general Hilbertian application remain outside the formalization.
-/
