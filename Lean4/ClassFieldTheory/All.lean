/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.Algebra.All
import ClassFieldTheory.AbstractClassFieldTheory.All
import ClassFieldTheory.AlgebraicNumberTheory.All
import ClassFieldTheory.Definitions.All
import ClassFieldTheory.GlobalClassFieldTheory.All
import ClassFieldTheory.HasseArf
import ClassFieldTheory.KroneckerWeber.All
import ClassFieldTheory.KummerTheory.All
import ClassFieldTheory.LocalClassFieldTheory.All
import ClassFieldTheory.LocalFieldTheory.All
import ClassFieldTheory.LubinTate.All
import ClassFieldTheory.RamificationTheory.All
import ClassFieldTheory.Theorems.All

/-!
# Class field theory

This is the canonical entry point for the class field theory library.
Its import closure is the complete production-library inventory.

The library contains local class field theory and global class field theory
for number fields, including the Hilbert product formula, general
power-residue reciprocity, and Gauss quadratic reciprocity, together with the
Hasse--Arf and Kronecker--Weber theorems. Shared valuation, ramification,
cohomology, Kummer, local-field, and Lubin--Tate infrastructure lives beside
those theories rather than under a theorem-specific directory.

For a smaller production dependency closure, import
`LocalClassFieldTheory`, `GlobalClassFieldTheory`, `HasseArf`, or
`KroneckerWeber` directly.
-/
