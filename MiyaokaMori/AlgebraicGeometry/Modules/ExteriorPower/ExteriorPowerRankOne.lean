import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestrictionIso
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerFiniteFree

/-! # The top exterior power of a locally free module of rank `n` has rank one

If a sheaf of modules is locally free of rank `n`, its `n`-th exterior power is locally free of
rank one.

Proof, on each local frame:
1. use the isomorphism between the exterior power of the restriction and the restriction of the
   exterior power;
2. transport the frame to the standard finite free sheaf and use the top exterior power isomorphism;
3. conclude with the standard isomorphism between the unit sheaf and the free sheaf of rank one.

Source: Stacks Project, `modules.tex`; cf. `TopExteriorLocalFrame`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Divisors AlgebraicGeometry.Proj AlgebraicGeometry.Scheme.Modules

namespace MiyaokaMori

universe u

variable {k : Type u} [Field k]

/-- The `n`-th exterior power of a locally free module of rank `n` is locally free of rank one. -/
theorem moduleExteriorPower_rank_one_clean (X : AlgebraicGeometry.Proj.SchemeOver k)
    (M : X.scheme.Modules) (n : ℕ)
    (hM : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank X M n) :
    AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank X (AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X.scheme M n) 1 := by
  constructor
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.local_frame x
  let eRestr :=
    MiyaokaMori.ExteriorPowerRestrictionIso.moduleExteriorPowerRestrictIso X.scheme U M n
  let eExt := AlgebraicGeometry.Scheme.Modules.moduleExteriorIso U.toScheme n e
  let eFree := MiyaokaMori.ExteriorPowerFiniteFree.moduleExteriorPowerFiniteFreeIso U.toScheme n
  refine ⟨U, hxU, ⟨eRestr ≪≫ eExt ≪≫ eFree ≪≫
    (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).symm⟩⟩

end MiyaokaMori
