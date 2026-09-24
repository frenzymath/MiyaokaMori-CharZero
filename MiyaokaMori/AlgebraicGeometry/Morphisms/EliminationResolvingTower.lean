import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.RingTheory.RegularLocalRing.RegularLocalDimLeTwoUFD
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerAvoiding
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerIsOver
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SurfaceClosedPointRegularDimTwo
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0ahh
import MiyaokaMori.AlgebraicGeometry.Blowup.BaseIdealOfPartialMap
import MiyaokaMori.AlgebraicGeometry.Blowup.BaseIdealExtension
import MiyaokaMori.AlgebraicGeometry.Morphisms.PartialMapExtendOfDomainTop
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedImmersionLiftOfDense
import MiyaokaMori.AlgebraicGeometry.Blowup.PointBlowupFiniteSupport

/-! # Elimination of indeterminacy by a tower of point blowups

Debarre, *Introduction to Mori theory*, Theorem 5.18 (with projective target): let `φ` be a rational
map from a smooth projective surface `W` to a projective `k`-scheme `Y` whose indeterminacy locus is a
finite set of closed points. Then there is a tower of point blowups `β : S → W`, all centres lying over
the indeterminacy points, and a morphism `Ψ : S → Y` with `Ψ = φ ∘ β` on all of `β⁻¹(dom φ)`.

Proof: form the base ideal `I` (whose cosupport lies in the indeterminacy set); by Stacks Project,
Tag 0AHH, a tower of point blowups makes `I · O_S` invertible (this replaces the descending induction on
`(D²)` in Debarre's proof); Hartshorne, Chapter II, Example 7.17.3 then extends the map to `P^N`; since
`Y` is closed in `P^N`, the extension lands in `Y`. This is the resolution step of
Corollary 4.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

/-- A proper `k`-scheme is (absolutely) separated. -/
theorem AlgebraicGeometry.Scheme.isSeparated_of_isProper_over_field {k : Type u} [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k))]
    [IsProper (Y ↘ Spec (CommRingCat.of k))] : Y.IsSeparated := by
  let _ : IsSeparated (Y ↘ Spec (CommRingCat.of k)) := IsProper.toIsSeparated
  constructor
  rw [← CategoryTheory.Limits.terminal.comp_from (Y ↘ Spec (CommRingCat.of k))]
  infer_instance

/-- A tower of point blowups of smooth projective surfaces is dominant. -/
theorem IsBlowupTower.isDominant {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} {β : S.toScheme ⟶ W.toScheme}
    (hβ : IsBlowupTower β) : IsDominant β := by
  induction hβ with
  | id W => infer_instance
  | step g hg p hp ih => infer_instance

/-- Elimination of indeterminacy (Debarre, Theorem 5.18): for a rational map `φ : W ⤏ Y` over `k` from a
smooth projective surface to a projective `k`-scheme, whose indeterminacy locus is a finite set of closed
points, there is a tower of point blowups `β : S → W` avoiding `dom φ` (all centres lie over the
indeterminacy points), dominant, and a morphism `Ψ : S → Y` agreeing with `φ ∘ β` on `β⁻¹(dom φ)`. -/
theorem exists_resolving_tower_agree {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of k))] [IsProper (Y ↘ Spec (CommRingCat.of k))] [Y.IsSeparated]
    (hY : IsProjectiveOver k Y)
    (φ : W.toScheme ⤏ Y) [φ.IsOver (Spec (CommRingCat.of k))]
    (hfin : ((φ.domain : Set W.toScheme)ᶜ).Finite)
    (hclosed : ∀ z ∈ ((φ.domain : Set W.toScheme)ᶜ), IsClosed ({z} : Set W.toScheme)) :
    ∃ (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ W.toScheme)
      (_ : IsBlowupTower β) (_ : IsBlowupTowerAvoiding β (φ.domain : Set W.toScheme))
      (_ : IsDominant β) (Ψ : S.toScheme ⟶ Y),
      (β ⁻¹ᵁ φ.domain).ι ≫ Ψ = (β ∣_ φ.domain) ≫ φ.toPartialMap.hom := by
  obtain ⟨N, i, hi, hiOver⟩ := hY
  have : IsClosedImmersion i := hi
  have : i.IsOver (Spec (CommRingCat.of k)) := hiOver
  have : (ProjectiveSpace N k).IsSeparated :=
    AlgebraicGeometry.Scheme.isSeparated_of_isProper_over_field (k := k) (ProjectiveSpace N k)
  let g0 : W.toScheme.PartialMap Y := φ.toPartialMap
  have : g0.IsOver (Spec (CommRingCat.of k)) := by infer_instance
  let g : W.toScheme.PartialMap (ProjectiveSpace N k) := g0.compHom i
  have : g.IsOver (Spec (CommRingCat.of k)) := by infer_instance
  let T : Set W.toScheme := (φ.domain : Set W.toScheme)ᶜ
  have hreg : ∀ x ∈ T, IsRegularLocalRing (W.toScheme.presheaf.stalk x) ∧
      ringKrullDim (W.toScheme.presheaf.stalk x) = 2 := fun x hx =>
    W.stalk_regular_dim_two x (hclosed x hx)
  obtain ⟨I, hIsupp, hIloc⟩ := ProjectiveSpace.exists_baseIdeal g T hfin hclosed
    (fun x hx => by
      have := (hreg x hx).1
      -- only the elementary version for dimension ≤ 2 is needed (steps 2–3 of the proof of
      -- Stacks 0AG0 together with 0AFT), not the general theorem that regular local rings are
      -- factorial (0AFZ / Auslander–Buchsbaum).
      exact IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two _
        (hreg x hx).2.le)
    (fun x hx => by
      have := (hreg x hx).1
      infer_instance)
    (fun x hx => (hreg x hx).2.le)
  have hIfin : (I.support : Set W.toScheme).Finite := hfin.subset hIsupp
  obtain ⟨S, β, hβ, havoid, D, hD⟩ := exists_pointBlowupTower_invertible W I hIfin
  have hβd : IsDominant β := hβ.isDominant
  have : β.IsOver (Spec (CommRingCat.of k)) := hβ.isOver
  have hd : Dense ((β ⁻¹ᵁ g.domain : S.toScheme.Opens) : Set S.toScheme) :=
    Scheme.Hom.dense_preimage_of_isDominant β g.domain g.dense_domain
  have htop := ProjectiveSpace.pullbackAlong_domain_eq_top_of_comap_baseIdeal β g hd T
    (fun x hx => not_not.mp hx) I hIloc D hD
  obtain ⟨Ψ', hΨ'⟩ := (g.pullbackAlong β hd).exists_extension_of_domain_eq_top htop
  have hΨ'' : (β ⁻¹ᵁ φ.domain).ι ≫ Ψ' = ((β ∣_ φ.domain) ≫ g0.hom) ≫ i := by
    exact hΨ'.trans (Category.assoc (β ∣_ φ.domain) g0.hom i).symm
  obtain ⟨Ψ, hΨ⟩ := IsClosedImmersion.exists_lift_of_dense i Ψ' (β ⁻¹ᵁ φ.domain) hd
    ((β ∣_ φ.domain) ≫ g0.hom) hΨ''
  have havoid' : IsBlowupTowerAvoiding β (φ.domain : Set W.toScheme) := by
    unfold IsBlowupTowerAvoiding at *
    apply MiyaokaMori.Statement.IsPointBlowupSequenceOver.mono havoid
    intro x hx
    exact hIsupp (not_not.mp hx)
  refine ⟨S, β, hβ, havoid', hβd, Ψ, ?_⟩
  rw [← cancel_mono i, Category.assoc, hΨ, hΨ'']

end
