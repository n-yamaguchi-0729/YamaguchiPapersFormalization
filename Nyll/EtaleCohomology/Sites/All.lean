/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.Stalks
import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.Subcanonical
import Nyll.EtaleCohomology.Sites.ClosedNeighborhoods
import Nyll.EtaleCohomology.Sites.RestrictionStalks
import Nyll.EtaleCohomology.Sites.RestrictionAdjunction
import Nyll.EtaleCohomology.Sites.ClosedImmersionStalks
import Nyll.EtaleCohomology.Sites.ClosedImmersionExact
import Nyll.EtaleCohomology.Sites.ClosedAdjunction
import Nyll.EtaleCohomology.Sites.Localization
import Nyll.EtaleCohomology.Sites.EmptySections
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Nyll.EtaleCohomology.Sites.SetSheafFunctors
import Nyll.EtaleCohomology.Sites.SetPullbackComposition
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.EtaleCohomology.Sites.EtaleSlice
import Nyll.EtaleCohomology.Sites.LocallyDirectedCover
import Nyll.EtaleCohomology.Sites.RepresentablePullback
import Nyll.EtaleCohomology.Sites.ConstantRepresentable
import Nyll.EtaleCohomology.Sites.ConnectedConstants
import Nyll.EtaleCohomology.Sites.MateComparison
import Nyll.EtaleCohomology.Sites.ModuleSetComparison
import Nyll.EtaleCohomology.Sites.ModuleConstant
import Nyll.EtaleCohomology.Sites.ConstantPullback
import Nyll.EtaleCohomology.Sites.PullbackComposition
import Nyll.EtaleCohomology.Sites.PullbackStalks
import Nyll.EtaleCohomology.Sites.ExtensionByZero
import Nyll.EtaleCohomology.Sites.StalkAdjunction
import Nyll.EtaleCohomology.Sites.ExtensionByZeroStalks
import Nyll.EtaleCohomology.Sites.SheafAdjunction
import Nyll.EtaleCohomology.Sites.OpenAdjunction
import Nyll.EtaleCohomology.Sites.ConstantPresentation
import Nyll.EtaleCohomology.Sites.FiniteFreeLift
import Nyll.EtaleCohomology.Sites.ModuleRestriction
import Nyll.EtaleCohomology.Sites.HenselianLocal
import Nyll.EtaleCohomology.Sites.ProperLocalSections
import Nyll.EtaleCohomology.Sites.ClosedFiberFiniteLiftCover
import Nyll.EtaleCohomology.Sites.SetPullbackExact
import Nyll.EtaleCohomology.Sites.ZariskiRestriction
import Nyll.EtaleCohomology.Sites.ZariskiBaseChange
import Nyll.EtaleCohomology.Sites.ZariskiSectionEquality
import Nyll.EtaleCohomology.Sites.ZariskiModuleBaseChange
import Nyll.EtaleCohomology.Sites.ZariskiGeometricStalks
import Nyll.EtaleCohomology.Sites.PullbackSections
import Nyll.EtaleCohomology.Sites.ClosedFiberFinitePullbackLifts
import Nyll.EtaleCohomology.Sites.ClosedZariskiComparison
import Nyll.EtaleCohomology.Sites.PullbackClosedFiberStalks
import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
import Nyll.EtaleCohomology.Sites.PullbackGlobalSectionsComposition
import Nyll.EtaleCohomology.Sites.ProperPullbackClosedUnitInjective
import Nyll.EtaleCohomology.Sites.ClosedFiberPullbackGluing
import Nyll.EtaleCohomology.Sites.CechSections
import Nyll.EtaleCohomology.Sites.FiniteRefinementCompatibleLift
import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
import Nyll.EtaleCohomology.Sites.FinitePushforwardStalks
import Nyll.EtaleCohomology.Sites.PullbackUnitStalks
import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
import Nyll.EtaleCohomology.Sites.FiniteSurjectiveUnit
import Nyll.EtaleCohomology.Sites.PushforwardStalkComposition
import Nyll.EtaleCohomology.Sites.PullbackStalkComposition
import Nyll.EtaleCohomology.Sites.PushforwardGlobalSections
import Nyll.EtaleCohomology.Sites.FiniteCechStalkLift
import Nyll.EtaleCohomology.Sites.SectionImageGluing
import Nyll.EtaleCohomology.Sites.FiniteSurjectiveDescent
import Nyll.EtaleCohomology.Sites.ProperHenselianH0


import Nyll.EtaleCohomology.Sites.FieldFiniteCover

import Nyll.EtaleCohomology.Sites.GaloisSections
