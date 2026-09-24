import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroData
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt

/-! # The nonvanishing open set of the coordinate sections near the zero section

Statement: the union of the pointwise nonvanishing loci of the coordinate sections `P` is an open set `U`;
at every point of `U` at least one coordinate section is nonzero, and since (by `hzero`) the coordinates
restricted to the zero section are the homogeneous coordinates, which have no common zero, the whole zero
section is contained in `U`. This is a step in the proof of Theorem 4.2 of the paper (the
morphism defined near the zero section).

Proof. Write `T := Tot(L)`, `p : T → C̃` its projection,
`σ : C̃ → T` the zero section, `Nb := ρ^* f^* O_X(1)` and `M := p^* Nb` (a line bundle on `T`,
`IsLineBundle.pullback`).
1. `U := ⨆ ℓ, M.nonvanishingLocus (P ℓ)` (`nonvanishingLocus` is open by Stacks 01CY,
   `isOpen_setOf_germ_notMem_maximalIdeal_smul`); `v ∈ U ↔ ∃ ℓ, ¬ IsZeroAt (P ℓ) v`
   (`Opens.mem_iSup`, `mem_nonvanishingLocus` is `Iff.rfl`).
2. For `v : U.toScheme`, `U.ι v = v.1 ∈ U`, so some `P ℓ` is nonzero at `v.1`; pulling back along the
   open immersion `U.ι` keeps it nonzero (`not_isZeroAt_sectionPullbackAlong`).
3. For `c : C̃`, `D.hcoord.1 (ρ c)` gives `i` with `coord i` nonzero at `ρ c`. Suppose `P i` were zero at
   `σ c`. Then `σ^* P i` is zero at `c` (`isZeroAt_sectionPullbackAlong_of_isZeroAt`), hence so is
   `restrictToZeroSection L (P i) = θ (σ^* P i)` for the canonical iso `θ : σ^* p^* Nb ≅ Nb`
   (`isZeroAt_map`: a morphism of module sheaves preserves `IsZeroAt`); by `hzero` this is
   `ρ^*(eqToHom (coord i))`, so `eqToHom (coord i)` is zero at `ρ c`
   (`isZeroAt_of_isZeroAt_sectionPullbackAlong`); applying `isZeroAt_map` to the inverse `eqToHom`
   (`eqToHom_trans`, `Functor.map_id`) shows `coord i` is zero at `ρ c`, contradiction. Hence `σ c ∈ U`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

/-- The nonvanishing open set `U ⊆ Tot(L)` of the coordinate sections `P`: at every point of `U` some
coordinate section is nonzero, and `U` contains the zero section (see the module docstring). -/
theorem morphism_near_zero_nonvanishing_open_core {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {rho : FiniteCover k C}
    {L : LineBundle rho.source.toVariety} {kappa : ℕ} (jet : BasedJet f rho L kappa)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ =
      restrictToThickening L (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety)
        rho.hom (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) kappa
        (P ℓ))
    (hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ) =
      sectionPullbackAlong rho.hom
        ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom
          (D.coord ℓ)))
    (hvanish : ∀ j, evalHomogeneousAtSections _ (D.E.F j) (D.E.homogeneous j) P = 0) :
    ∃ (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens),
      (∀ v : U.toScheme, ∃ ℓ, ¬ IsZeroAt (sectionPullbackAlong U.ι (P ℓ)) v) ∧
      Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base ⊆
        (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left) := by
  -- notation
  let Nb : rho.source.toScheme.Modules :=
    (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
  let M : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules :=
    (AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj Nb
  -- Step 1: the open set
  let U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens :=
    ⨆ ℓ, M.nonvanishingLocus (P ℓ)
  have hmemU : ∀ v, v ∈ U ↔ ∃ ℓ, ¬ IsZeroAt (P ℓ) v := fun v => by
    rw [TopologicalSpace.Opens.mem_iSup]
    rfl
  refine ⟨U, ?_, ?_⟩
  · -- Step 2
    intro v
    obtain ⟨ℓ, hℓ⟩ := (hmemU _).mp v.2
    exact ⟨ℓ, not_isZeroAt_sectionPullbackAlong U.ι M (P ℓ) v hℓ⟩
  · -- Step 3
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, hmemU]
    obtain ⟨i, hi⟩ := D.hcoord.1 (rho.hom.base c)
    refine ⟨i, fun hz => hi ?_⟩
    have h1 : IsZeroAt (sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection L.toModules)
        (P i)) c :=
      isZeroAt_sectionPullbackAlong_of_isZeroAt _ M (P i) c hz
    let θ : (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.zeroSection L.toModules)).obj M ≅ Nb :=
      (AlgebraicGeometry.Scheme.Modules.pullbackComp
        (AlgebraicGeometry.Scheme.zeroSection L.toModules)
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).app Nb ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (AlgebraicGeometry.Scheme.zeroSection_comp L.toModules)).app Nb ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId rho.source.toScheme).app Nb
    have h2 : IsZeroAt (AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P i)) c :=
      isZeroAt_map θ.hom _ c h1
    rw [hzero i] at h2
    have h3 := isZeroAt_of_isZeroAt_sectionPullbackAlong rho.hom _ _ c h2
    have h4 := isZeroAt_map ((AlgebraicGeometry.Scheme.Modules.pullback f).map
      (CategoryTheory.eqToHom (X.OX_toModules 1))) _ _ h3
    change IsZeroAt ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1).symm) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1))).val.app (Opposite.op ⊤)).hom (D.coord i)) _ at h4
    rw [← CategoryTheory.Functor.map_comp, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id] at h4
    exact h4

end
