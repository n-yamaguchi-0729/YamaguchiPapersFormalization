/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocity
import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocityQuotient
import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianReciprocityQuotientEquivMk
import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceLocalGlobalNormKernel
import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinNormKernel
import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinDecomposition
import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceCompletionLocalArtin
import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinLocalValue
import ClassFieldTheory.Theorems.GlobalClassFieldTheory.TopologicalGlobalReciprocity
import ClassFieldTheory.Theorems.GlobalClassFieldTheory.MaximalAbelianGlobalArtin

/-!
# Global class field theory

This module collects finite ideal-theoretic reciprocity and the topological
maximal-abelian statements. The latter are proved via topological comparison
with the existing restricted-product implementation.
-/

