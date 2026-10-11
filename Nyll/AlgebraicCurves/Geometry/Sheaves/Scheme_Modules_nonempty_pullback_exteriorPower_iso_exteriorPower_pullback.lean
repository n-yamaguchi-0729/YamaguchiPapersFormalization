/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.SchemeTheory.Sheaves.RestrictOpen

/-!
# Pullback to an open commutes with exterior powers

Restriction commutes with presheaf exterior powers, and sheafification transports
this comparison to pullback of module sheaves.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback

universe u

open CategoryTheory

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Restriction along the open indexing functor commutes with presheaf exterior powers. -/
noncomputable def restrictPresheaf₀CompPresheafExteriorPowerIso (n : ℕ) (U : X.Opens) :
    presheafExteriorPower X n ⋙ restrictPresheaf₀ U ≅
      restrictPresheaf₀ U ⋙ presheafExteriorPower (U : Scheme.{u}) n :=
  NatIso.ofComponents
    (fun P => PresheafOfModules.isoMk (fun V => Iso.refl _) (fun V W f => by
      simp only [Iso.refl_hom]
      rfl))
    (fun φ => by
      ext V : 1
      simp only [Functor.comp_map, PresheafOfModules.comp_app]
      rfl)

/-- The restriction comparison transported to the ring-sheaf restriction functor. -/
noncomputable def restrictPresheafCompPresheafExteriorPowerIso (n : ℕ) (U : X.Opens) :
    presheafExteriorPower X n ⋙ restrictPresheaf U ≅
      restrictPresheaf U ⋙ presheafExteriorPower (U : Scheme.{u}) n :=
  Functor.isoWhiskerLeft _ (restrictPresheafIsoRestrictPresheaf₀ U) ≪≫
    restrictPresheaf₀CompPresheafExteriorPowerIso n U ≪≫
    Functor.isoWhiskerRight (restrictPresheafIsoRestrictPresheaf₀ U).symm _

section steps
variable (n : ℕ) (U : X.Opens) (M : X.Modules)

/-- The comparison between pullback of the sheafified power and sheafified restriction. -/
noncomputable def pullbackExteriorPowerIso_step1 :
    (Modules.pullback U.ι).obj ((exteriorPower X n).obj M) ≅
      (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((restrictPresheaf U).obj ((presheafExteriorPower X n).obj M.val)) :=
  (sheafificationCompPullbackIso U).app ((presheafExteriorPower X n).obj M.val)

/-- The sheafified comparison between exterior power before and after restriction. -/
noncomputable def pullbackExteriorPowerIso_step2 :
    (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((restrictPresheaf U).obj ((presheafExteriorPower X n).obj M.val)) ≅
      (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((presheafExteriorPower (U : Scheme.{u}) n).obj ((restrictPresheaf U).obj M.val)) :=
  (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).mapIso
    ((restrictPresheafCompPresheafExteriorPowerIso n U).app M.val)

/-- The sheafified restricted power identified with the exterior power of the restriction. -/
noncomputable def pullbackExteriorPowerIso_step25 :
    (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((presheafExteriorPower (U : Scheme.{u}) n).obj ((restrictPresheaf U).obj M.val)) ≅
      (exteriorPower (U : Scheme.{u}) n).obj ((restrictOpen U).obj M) :=
  Iso.refl _

/-- The exterior-power comparison induced by the restriction-pullback isomorphism. -/
noncomputable def pullbackExteriorPowerIso_step3 :
    (exteriorPower (U : Scheme.{u}) n).obj ((restrictOpen U).obj M) ≅
      (exteriorPower (U : Scheme.{u}) n).obj ((Modules.pullback U.ι).obj M) :=
  (exteriorPower (U : Scheme.{u}) n).mapIso ((restrictOpenIsoPullback U).app M)

end steps

/-- The canonical isomorphism commuting pullback to the open with exterior power. -/
noncomputable def pullbackExteriorPowerIso (n : ℕ) (U : X.Opens) (M : X.Modules) :
    (Modules.pullback U.ι).obj ((exteriorPower X n).obj M) ≅
      (exteriorPower (U : Scheme.{u}) n).obj ((Modules.pullback U.ι).obj M) :=
  pullbackExteriorPowerIso_step1 n U M ≪≫ pullbackExteriorPowerIso_step2 n U M ≪≫
    pullbackExteriorPowerIso_step25 n U M ≪≫ pullbackExteriorPowerIso_step3 n U M

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
  {X : Scheme.{u}} (n : ℕ) (U : X.Opens) (M : X.Modules) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.exteriorPower X n).obj M) ≅
      (Scheme.Modules.exteriorPower (U : Scheme.{u}) n).obj ((Scheme.Modules.pullback U.ι).obj M))
          :=
  ⟨Scheme.Modules.pullbackExteriorPowerIso n U M⟩
end Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply
    PresheafOfModules.pushforwardNatTrans_app_app_apply
    PresheafOfModules.pushforwardCongr_hom_app_app_apply
