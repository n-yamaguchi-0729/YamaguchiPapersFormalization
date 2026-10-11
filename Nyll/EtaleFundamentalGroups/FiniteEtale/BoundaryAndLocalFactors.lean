/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.FinitePresentationExtension
import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.GenericTensor.IntegralClosureBaseChange
import Nyll.EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericTensor.NormalizationPrime
import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.Complement
import Nyll.EtaleFundamentalGroups.FiniteEtale.ChosenPrime.Henselian.BoundaryAwayNoetherian
import Nyll.EtaleFundamentalGroups.FiniteEtale.ChosenPrime.PointedBase.BoundaryAway
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.ComponentDimensionTwo
import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenLocalizationEtale
import Nyll.SchemeTheory.FiniteEtale.Henselian.ResidueTrivialFiniteEtale
import Nyll.EtaleFundamentalGroups.FiniteEtale.HenselianAscent
import Nyll.SchemeTheory.FiniteEtale.Local.OfTargetLocalizations
import Nyll.EtaleFundamentalGroups.FiniteEtale.Local.OverDiscreteValuationRing
import Nyll.EtaleFundamentalGroups.FiniteEtale.Towers.IntegralTargetBoundaryAway

/-!
# Boundary étaleness and local factors

Away, chosen-prime, Henselian, and local finite-étale results used in one-point inertia arguments.
-/
