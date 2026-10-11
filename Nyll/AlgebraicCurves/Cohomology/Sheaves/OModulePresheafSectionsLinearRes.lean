/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech

/-!
# OModule Presheaf Sections Linear Res
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)

/-- The section module with scalars restricted along the ring restriction homomorphism. -/
@[reducible] def moduleRestrict {U U' : V.Opens} (h : U ≤ U') : Module Γ(V, U') (F.obj U) :=
  Module.compHom (F.obj U) (V.presheaf.map (homOfLE h).op).hom

/-- The restriction map viewed as linear over sections on the larger open. -/
def resₗ {U U' : V.Opens} (h : U ≤ U') :
    letI := F.moduleRestrict h
    F.obj U' →ₗ[Γ(V, U')] F.obj U :=
  letI := F.moduleRestrict h
  { toFun := F.res h
    map_add' := map_add _
    map_smul' := fun a x => F.res_smul h a x }

theorem resₗ_apply {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') :
    letI := F.moduleRestrict h
    F.resₗ h x = F.res h x := rfl

theorem moduleRestrict_smul_def {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U')) (x : F.obj U) :
    letI := F.moduleRestrict h
    a • x = (V.presheaf.map (homOfLE h).op).hom a • x := rfl

end AlgebraicGeometry.OModulePresheaf

end
