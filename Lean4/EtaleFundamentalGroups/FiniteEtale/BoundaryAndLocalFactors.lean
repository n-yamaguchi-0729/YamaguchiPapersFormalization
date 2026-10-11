/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import EtaleFundamentalGroups.FiniteEtale.Away.FinitePresentationExtension
import EtaleFundamentalGroups.FiniteEtale.Away.GenericTensor.IntegralClosureBaseChange
import EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericTensor.NormalizationPrime
import EtaleFundamentalGroups.FiniteEtale.Boundary.Complement
import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.Henselian.BoundaryAwayNoetherian
import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.PointedBase.BoundaryAway
import EtaleFundamentalGroups.FiniteEtale.GenericFiber.ComponentDimensionTwo
import SchemeTheory.FiniteEtale.Henselian.ChosenLocalizationEtale
import SchemeTheory.FiniteEtale.Henselian.ResidueTrivialFiniteEtale
import EtaleFundamentalGroups.FiniteEtale.HenselianAscent
import SchemeTheory.FiniteEtale.Local.OfTargetLocalizations
import EtaleFundamentalGroups.FiniteEtale.Local.OverDiscreteValuationRing
import EtaleFundamentalGroups.FiniteEtale.Towers.IntegralTargetBoundaryAway

/-!
# Boundary étaleness and local factors

Away, chosen-prime, Henselian, and local finite-étale results used in one-point inertia arguments.
-/
