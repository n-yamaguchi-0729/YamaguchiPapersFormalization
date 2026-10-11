/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.AdjoinRoot.All
import EtaleFundamentalGroups.Kummer.Boundary.All
import EtaleFundamentalGroups.Kummer.Completions.All
import EtaleFundamentalGroups.Kummer.Descent.All
import EtaleFundamentalGroups.Kummer.FieldTowers.All
import EtaleFundamentalGroups.Kummer.GenericTensor.All
import EtaleFundamentalGroups.Kummer.Henselian.All
import EtaleFundamentalGroups.Kummer.HigherRadical.All
import EtaleFundamentalGroups.Kummer.IteratedRadical.All
import EtaleFundamentalGroups.Kummer.Lattices.All
import EtaleFundamentalGroups.Kummer.Laurent.All
import EtaleFundamentalGroups.Kummer.LocalGeometry.All
import EtaleFundamentalGroups.Kummer.Main
import EtaleFundamentalGroups.Kummer.NormalCrossings.All
import EtaleFundamentalGroups.Kummer.Normalization.All
import EtaleFundamentalGroups.Kummer.Obstructions.All
import EtaleFundamentalGroups.Kummer.PureRadical.All
import EtaleFundamentalGroups.Kummer.Radicals.All
import EtaleFundamentalGroups.Kummer.RootCovers.All
import EtaleFundamentalGroups.Kummer.SelectedRoot.All
import EtaleFundamentalGroups.Kummer.UnitAbsorption.All
import EtaleFundamentalGroups.Kummer.GenericCharacterRootCover
import EtaleFundamentalGroups.Kummer.GenericEtaleDivisibility
import EtaleFundamentalGroups.Kummer.OpenGenericEtaleDivisibility

/-!
# Kummer covers for one-point inertia

Radical covers, selected components, completion arguments, and strict-normal-crossings terminals.
-/


/-! Canonical aggregate for EtaleFundamentalGroups.Kummer. -/
