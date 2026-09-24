import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface

/-! # Towers of point blowups are surjective

A tower of point blowups is surjective: each point blowup is proper and dominant, hence surjective
(Stacks 02OS: the blowup is an isomorphism away from the centre; the preimage of the centre is the
nonempty exceptional curve).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- A single point blowup `π : Bl_p S → S` is surjective. Proof: `Bl_p S` is projective over `k`, hence
proper (`isProjectiveOver_iff_isProper_and_isAmple`), and `S` is separated over `k`, so `π` is proper
(`IsProper.of_comp`; `π ≫ (S ↘ Spec k) = Bl_p S ↘ Spec k` holds by `rfl`); `π` is dominant since it is an
isomorphism over the dense open `S ∖ {p}`; a universally closed dominant morphism is surjective
(`Surjective.of_universallyClosed_of_isDominant`). -/
theorem pointBlowup.π_surjective {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.Surjective (pointBlowup.π S p hp) := by
  have hproperSource : AlgebraicGeometry.IsProper
      ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ((isProjectiveOver_iff_isProper_and_isAmple k _).mp
      (pointBlowup S p hp).toSmoothProjectiveVariety.projective).1
  have hcomp : pointBlowup.π S p hp ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := rfl
  have hproperComp : AlgebraicGeometry.IsProper
      (pointBlowup.π S p hp ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
    rw [hcomp]
    exact hproperSource
  have : AlgebraicGeometry.IsProper (pointBlowup.π S p hp) :=
    AlgebraicGeometry.IsProper.of_comp (pointBlowup.π S p hp)
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  infer_instance

/-- A tower of point blowups (a composite of finitely many point blowups) is surjective: by induction on
`IsBlowupTower`, the identity is surjective, each step is surjective by `pointBlowup.π_surjective`, and
surjectivity is stable under composition. -/
theorem IsBlowupTower.surjective {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} {β : S.toScheme ⟶ W.toScheme}
    (hβ : IsBlowupTower β) : AlgebraicGeometry.Surjective β := by
  induction hβ with
  | id W => infer_instance
  | step g hg p hp ih =>
    have h1 := pointBlowup.π_surjective _ p hp
    have h2 := ih
    infer_instance

end
