/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenPlaceTransport
import Nyll.EtaleFundamentalGroups.Kummer.OpenGenericEtaleDivisibility
import Nyll.JacobianVarieties.Kummer.OpenDivisorResidues

/-!
# Actual finite étale Kummer roots are unramified away from the boundary

The condition defining the divisorial open Kummer group is proved from the
actual cover, using the actual local rings of the open curve.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

theorem mem_openKummerUnits_of_finiteEtale_generic_root
    (M : CurveModel K F) {X : Scheme} [IsIntegral X]
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (L : Type) [Field L] [Algebra X.functionField L]
    {Y : Scheme} (f : Y ⟶ X) [IsFinite f] [Etale f]
    (e : pullback f (X.fromSpecStalk (genericPoint X)) ≅ Spec (.of L))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) =
      pullback.snd f (X.fromSpecStalk (genericPoint X)))
    (a : X.functionFieldˣ) (b : L) (n : ℕ+)
    (hb : b ^ (n : ℕ) = algebraMap X.functionField L (a : X.functionField)) :
    Units.map (M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion).symm.toMonoidHom a ∈
      Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n := by
  let : Algebra K X.functionField := (baseToFunctionField (j ≫ M.toBase)).toAlgebra
  have : SmoothOfRelativeDimension 1 (j ≫ M.toBase) :=
    smoothOfRelativeDimension_comp 0 1 j M.toBase
  let E := M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion
  obtain ⟨Φ, hord, hstalk⟩ := M.exists_openPlaceEquiv_stalk_range_ord j
  intro v hv
  obtain ⟨x, hx⟩ := hstalk v hv
  have hd := EtaleFundamentalGroups.ord_dvd_of_finiteEtale_generic_root_on_smoothCurve
    K (j ≫ M.toBase) L f e he (a : X.functionField) b (n : ℕ) hb x (Φ v) hx
  have ho := hord v (E.symm (a : X.functionField))
  change (Φ v).ord (E (E.symm (a : X.functionField))) =
    v.ord (E.symm (a : X.functionField)) at ho
  rw [E.apply_symm_apply] at ho
  change (n : ℤ) ∣ v.ord (E.symm (a : X.functionField))
  rw [← ho]
  exact hd

end AlgebraicCurve.CurveModel
