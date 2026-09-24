import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroData
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodZeroSectionSurjective
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroSectionCompat
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroJetCompat

/-! # Compatibility of the morphism near the zero section with the jet

Statement: given a morphism `Phi0` on a neighbourhood of the zero section obtained by projectivizing the tuple of
sections `P`, and given that the zero section is contained in that neighbourhood, `Phi0` realizes the given based
jet: its restriction to the zero section is `rho.hom ≫ f`, and its restriction to the jet neighbourhood, after
factoring the jet through the punctured cone, is `jetx ≫ MMSetup.toX f`.

Proof:
1. `sigma0 := IsOpenImmersion.lift U.ι zeroSection` (the range condition is `hU0`, via `Opens.range_ι`);
2. `nu := IsOpenImmersion.lift U.ι (jetNeighborhood.toTotalSpace L κ).left`: every point of the jet neighbourhood
   is a zero-section point, and `zeroSection ≫ toTotalSpace` is the zero section of `Tot`
   (`jetNeighborhood.zeroSection_toTotalSpace`), so the image lies in `U`;
3. `jetx := IsOpenImmersion.lift (MMSetup.punctured f).ι jet.hom`: again pointwise, `jet.hom (σ c) = (ρ ≫ s) c`
   (`jet.restrict`), and the seed section `s` lies in the punctured cone (`seedSection_mem_punctured`);
4. `sigma0 ≫ Phi0 = rho.hom ≫ f`;
5. `nu ≫ Phi0 = jetx ≫ MMSetup.toX f` (`morphism_near_zero_jet_compat`).
Used in the proof of Theorem 4.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

-- `hvanish` is part of the interface of `IsTupleProjectivization`; it is not needed here.
set_option linter.unusedVariables false in
theorem morphism_near_zero_jet_compatibility_core {k : Type u} [Field k]
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
    (hvanish : ∀ j, evalHomogeneousAtSections _ (D.E.F j) (D.E.homogeneous j) P = 0)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Phi0 : U.toScheme ⟶ X.toScheme)
    (hPhi : IsTupleProjectivization
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules)
      P U Phi0)
    (hU0 : Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base ⊆
      (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left)) :
    RealizesJet jet U Phi0 := by
  have hUι : Set.range U.ι.base =
      (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left) :=
    AlgebraicGeometry.Scheme.Opens.range_ι U
  -- (1) the zero section lands in U
  have h0 : Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base ⊆
      Set.range U.ι.base := by
    rw [hUι]; exact hU0
  -- (2) the jet neighbourhood lands in U: its points are the zero-section points
  have hnu : Set.range (jetNeighborhood.toTotalSpace L kappa).left.base ⊆
      Set.range U.ι.base := by
    rw [hUι]
    rintro _ ⟨y, rfl⟩
    obtain ⟨c, rfl⟩ := jetNeighborhood.zeroSection_base_surjective L kappa y
    have hc : (jetNeighborhood.toTotalSpace L kappa).left.base
        ((jetNeighborhood.zeroSection L kappa).base c) =
        (jetNeighborhood.zeroSection L kappa ≫ (jetNeighborhood.toTotalSpace L kappa).left).base c :=
      rfl
    rw [hc, jetNeighborhood.zeroSection_toTotalSpace]
    exact hU0 ⟨c, rfl⟩
  -- (3) the jet lands in the punctured cone: on the zero section it is ρ ≫ s, and s ∈ Z^×
  have hjetx : Set.range jet.hom.base ⊆ Set.range (MMSetup.punctured f).ι.base := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨c, rfl⟩ := jetNeighborhood.zeroSection_base_surjective L kappa y
    obtain ⟨s', hs2⟩ : ∃ s' : C.toScheme ⟶ (MMSetup.punctured f).toScheme,
        s' ≫ (MMSetup.punctured f).ι = (MMSetup.seed f).1 :=
      seedSection_mem_punctured X.embedding D.E f D.coord D.hcoord D.E.deg_pos
        (seedSection_equations_vanish X.embedding D.E f D.coord D.hcoord)
    refine ⟨(rho.hom ≫ s').base c, ?_⟩
    have key : (rho.hom ≫ s') ≫ (MMSetup.punctured f).ι =
        jetNeighborhood.zeroSection L kappa ≫ jet.hom := by
      rw [Category.assoc, hs2, jet.restrict]
    exact congrArg (fun g : rho.source.toScheme ⟶ (MMSetup.cone f).left => g.base c) key
  refine ⟨hU0, AlgebraicGeometry.IsOpenImmersion.lift U.ι _ h0,
    AlgebraicGeometry.IsOpenImmersion.lift U.ι _ hnu,
    AlgebraicGeometry.IsOpenImmersion.lift (MMSetup.punctured f).ι jet.hom hjetx,
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _, ?_,
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _, ?_⟩
  · exact morphism_near_zero_zeroSection_compat P hzero U Phi0 hPhi _
      (AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _)
  · exact morphism_near_zero_jet_compat jet P hjet U Phi0 hPhi _
      (AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _) _
      (AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _)

end
