/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Theorem1Dot1AbFaithfulness
import Yamaguchi26AbfaithfulGalois.Theorem1Dot2PrimeOrderTest
import Yamaguchi26AbfaithfulGalois.Theorem1Dot3SigmaProperties
import Yamaguchi26AbfaithfulGalois.Theorem2Dot1ElementarySplitCriterion
import Yamaguchi26AbfaithfulGalois.Theorem3Dot1PrimePowerRoots
import Yamaguchi26AbfaithfulGalois.Theorem3Dot3FiniteOrderModP
import Yamaguchi26AbfaithfulGalois.Theorem3Dot4PrincipalUnitLogarithm
import Yamaguchi26AbfaithfulGalois.Theorem3Dot5CompletePrimeDegree
import Yamaguchi26AbfaithfulGalois.Theorem3Dot6MixedCharacteristic
import Yamaguchi26AbfaithfulGalois.Theorem4Dot1ResidueZeroLift
import Yamaguchi26AbfaithfulGalois.Theorem4Dot2HigherLocalFields
import Yamaguchi26AbfaithfulGalois.Theorem5Dot1FaithfulAbelianExtension
import Yamaguchi26AbfaithfulGalois.Theorem5Dot2AbelianSplitSolvableSlim
import Yamaguchi26AbfaithfulGalois.Theorem6Dot1FormalHilbert90
import Yamaguchi26AbfaithfulGalois.Theorem6Dot2IntegralInvariants
import Yamaguchi26AbfaithfulGalois.Theorem6Dot3CentralizerCriterion
import Yamaguchi26AbfaithfulGalois.Theorem6Dot4RelativeCriterion
import Yamaguchi26AbfaithfulGalois.Theorem6Dot5GroupCriterion
import Yamaguchi26AbfaithfulGalois.Theorem6Dot6AbsoluteCenter
import Yamaguchi26AbfaithfulGalois.Theorem6Dot7FieldSlimExamples
import Yamaguchi26AbfaithfulGalois.GroupTheory.All
import Yamaguchi26AbfaithfulGalois.HigherLocalField.All
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.All
import Yamaguchi26AbfaithfulGalois.FieldExamples.All
import Yamaguchi26AbfaithfulGalois.Kummer.All
import Yamaguchi26AbfaithfulGalois.Analytic.All

/-!
# Ab-faithfulness of absolute Galois groups

Formalization of `AbfatifhulGalois.tex` (source checked 2026-10-05).

Scope: the numbered statements in Sections 1--6, including the conclusions of
Example 6.7(1)--(3), except Example 2.2 in its entirety and the final PAC lemma
6.8 (`ex:slim-perfect-kernel`). The Hilbertian application after Proposition 5.2
uses the Ikeda theorem cited in the excluded Example 2.2.

Section 5 constructs faithful finite abelian extensions without increasing the
prescribed derived-length bound, and uses split embedding problems to prove slimness.
The numbered modules follow the current manuscript. Lemma 3.2 is supplied
by `Kummer.PrimeDegreeCohomology.prime_degree_cohomology_of_mixedChar`,
which proves its H¹ conclusion without the roots-of-unity hypothesis.
That stronger statement is intentionally kept in the foundation layer.
Other stronger results from the earlier manuscript are retained in
`GroupTheory`, `Kummer`, `FormalHilbert90`, `HigherLocalField`, and `FieldExamples`.
Example 6.7(2) is proved directly from its field embedding, using a mixed-
characteristic discrete valuation and finite primary roots in finite extensions.
-/

