/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Nyll.SchemeTheory.Descent.FGSubalgebra
import Nyll.AlgebraicCurves.Geometry.Schemes.FGSubalgebra_nonempty_isColimit_cocone

/-!
# Spectra of finitely generated subalgebras form an inverse limit

Applying the spectrum functor to the colimit presentation by finitely generated subalgebras
gives the canonical limit cone with the spectrum of the original algebra as its vertex.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.FGSubalgebra_nonempty_isLimit_specCone

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.FGSubalgebra.nonempty_isLimit_specCone
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (IsLimit (FGSubalgebra.specCone R A)) :=
  ⟨isLimitOfPreserves Scheme.Spec (FGSubalgebra.nonempty_isColimit_cocone R A).some.op⟩
end AlgebraicCurves.Geometry.Schemes.Proofs.FGSubalgebra_nonempty_isLimit_specCone
end ProofImplementation
