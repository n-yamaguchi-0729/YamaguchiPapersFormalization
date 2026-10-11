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

import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_correspondence_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_eq_of_baseAut_eq_of_forall_smul_place_eq
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_eq_of_forall_smul_place_eq
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_existsUnique_monoidHom_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_exists_baseAut_eq_of_constantFieldExtension
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_inertiaDeg_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_ofAlgAut_smul_place
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_ord_algebraMap_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pic0_correspondence_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pic0_correspondence_swap_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pullbackAlong_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pullback_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pushforwardAlong_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pushforward_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_ramificationIndex_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_restrict_smul
