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

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.All
import Nyll.AlgebraicCurves.Geometry.Curves.All
import Nyll.AlgebraicCurves.Geometry.Deformation.All
import Nyll.AlgebraicCurves.Geometry.Descent.All
import Nyll.AlgebraicCurves.Geometry.Picard.All
import Nyll.AlgebraicCurves.Geometry.Projective.All
import Nyll.AlgebraicCurves.Geometry.AlgHom_eq_of_forall_restrictAlong_eq_of_charZero
import Nyll.AlgebraicCurves.Geometry.Exists_D_ne_zero
import Nyll.AlgebraicCurves.Geometry.Exists_bounded_two_cochain_of_local_coboundaries
import Nyll.AlgebraicCurves.Geometry.Exists_coboundary_at_infinity_of_smallExtension_of_split
import Nyll.AlgebraicCurves.Geometry.Exists_disc_sections_locality_of_henselSections_of_weierstrassPreparation
import Nyll.AlgebraicCurves.Geometry.Exists_injective_ell_sub_sum_single_eq_zero_of_card_le
import Nyll.AlgebraicCurves.Geometry.Exists_int_forall_degree_add_one_sub_le_ell
import Nyll.AlgebraicCurves.Geometry.Exists_isRational_forall_mem_and_evalAt_eq_of_algHom
import Nyll.AlgebraicCurves.Geometry.Exists_local_coboundary_of_smallExtension_of_monogenic_fibre
import Nyll.AlgebraicCurves.Geometry.Exists_mul_eq_hochschild_coboundary_of_discr_ne_zero
import Nyll.AlgebraicCurves.Geometry.FundamentalIdentityAlong
import Nyll.AlgebraicCurves.Geometry.Inv_smul_D_eq_zero_iff_exists_pow_eq
import Nyll.AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint
import Nyll.AlgebraicCurves.Geometry.Map_ne_zero_of_tame
import Nyll.AlgebraicCurves.Geometry.Mem_of_mul_eval2_mem_of_forall_coeff_mem_maximalIdeal
import Nyll.AlgebraicCurves.Geometry.Nonempty_algEquiv_functionField_of_iso
import Nyll.AlgebraicCurves.Geometry.One_le_deg
import Nyll.AlgebraicCurves.Geometry.WeilReciprocity
import Nyll.AlgebraicCurves.Geometry.WeilReciprocity_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Schemes.All
import Nyll.AlgebraicCurves.Geometry.Sheaves.All
