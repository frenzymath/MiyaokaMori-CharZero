import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafSheafify
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.SheafOfUnits

/-! # Sections of the sheaf of rational functions and the function field

On an integral scheme, the map `𝒦_X(U) → K(X)` (`U` nonempty) from sections of the sheaf of rational
functions to the function field: on each open the presheaf of total quotient rings maps to `K(X)` by the
universal property of localization (a stalkwise nonzerodivisor has nonzero germ at the generic point);
these assemble into a presheaf morphism to the skyscraper sheaf at the generic point, which descends to
`𝒦_X` by the universal property of sheafification. Also the version for units `𝒦_X^*(U) → K(X)^*`. The
map is bijective (Stacks 01X5) and compatible with `O_X → 𝒦_X` and with restriction.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped nonZeroDivisors in

/-- The germ at the generic point of a stalkwise nonzerodivisor section is a unit of `K(X)` (a nonzerodivisor
in a field is nonzero). -/

theorem AlgebraicGeometry.Scheme.isUnit_germ_genericPoint_of_mem
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (V : X.Opens)
    (hV : genericPoint X ∈ V)
    (s : (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (Opposite.op V)) :
    IsUnit ((X.presheaf.germ V (genericPoint X) hV).hom s.1) := by
  have h := s.2
  simp only [TopCat.Presheaf.submonoidPresheafOfStalk_obj, Submonoid.mem_iInf, Submonoid.mem_comap] at h
  exact (isUnit_iff_ne_zero (G₀ := X.functionField)).mpr (nonZeroDivisors.ne_zero (h ⟨_, hV⟩))

open scoped nonZeroDivisors in

/-- Presheaf level: when `V` contains the generic point, the map `Q(O(V)) → K(X)` from the total quotient
ring (the lift of the germ map along the localization). -/

noncomputable def AlgebraicGeometry.Scheme.totalQuotientToFunctionField
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (V : X.Opens)
    (hV : genericPoint X ∈ V) :
    X.presheaf.totalQuotientPresheaf.obj (Opposite.op V) ⟶ X.functionField :=
  CommRingCat.ofHom
    (IsLocalization.lift
      (M := (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (Opposite.op V))
      (S := Localization
        ((X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (Opposite.op V)))
      (g := (X.presheaf.germ V (genericPoint X) hV).hom)
      (fun s => X.isUnit_germ_genericPoint_of_mem V hV s))

open scoped nonZeroDivisors in

/-- Universal property of localization: `O(V) → Q(O(V)) → K(X)` is the germ at the generic point. -/

theorem AlgebraicGeometry.Scheme.toTotalQuotientPresheaf_app_comp_totalQuotientToFunctionField
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (V : X.Opens)
    (hV : genericPoint X ∈ V) :
    X.presheaf.toTotalQuotientPresheaf.app (Opposite.op V) ≫ X.totalQuotientToFunctionField V hV =
      X.presheaf.germ V (genericPoint X) hV :=
  CommRingCat.hom_ext
    (IsLocalization.lift_comp
      (M := (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (Opposite.op V))
      (S := Localization
        ((X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (Opposite.op V)))
      (fun s => X.isUnit_germ_genericPoint_of_mem V hV s))

/-- Compatibility with restriction: `Q(O(V)) → Q(O(W)) → K(X)` equals `Q(O(V)) → K(X)` (`O(V) → Q(O(V))` is
an epimorphism, both sides are the germ map on `O(V)`, then `germ_res'`). -/

theorem AlgebraicGeometry.Scheme.totalQuotientPresheaf_map_totalQuotientToFunctionField
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] {V W : (X.Opens)ᵒᵖ}
    (f : V ⟶ W) (hW : genericPoint X ∈ W.unop) :
    X.presheaf.totalQuotientPresheaf.map f ≫ X.totalQuotientToFunctionField W.unop hW =
      X.totalQuotientToFunctionField V.unop (f.unop.le hW) := by
  have : Epi (X.presheaf.toTotalQuotientPresheaf.app V) := Localization.epi' _
  rw [← cancel_epi (X.presheaf.toTotalQuotientPresheaf.app V), ← Category.assoc,
    ← NatTrans.naturality, Category.assoc,
    X.toTotalQuotientPresheaf_app_comp_totalQuotientToFunctionField,
    X.toTotalQuotientPresheaf_app_comp_totalQuotientToFunctionField]
  exact X.presheaf.germ_res' f _ hW

/-- The presheaf of total quotient rings to the skyscraper sheaf with value `K(X)` at the generic point. -/

noncomputable def AlgebraicGeometry.Scheme.totalQuotientPresheafToSkyscraper
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] :
    open Classical in
    X.presheaf.totalQuotientPresheaf ⟶ skyscraperPresheaf (genericPoint X) X.functionField :=
  open Classical in
  { app := fun V =>
      if h : genericPoint X ∈ V.unop then
        X.totalQuotientToFunctionField V.unop h ≫ eqToHom (if_pos h).symm
      else ((if_neg h).symm.ndrec CategoryTheory.Limits.terminalIsTerminal).from _
    naturality := by
      classical
      intro V W f
      dsimp only [skyscraperPresheaf]
      by_cases hW : genericPoint X ∈ W.unop
      · have hV : genericPoint X ∈ V.unop := f.unop.le hW
        rw [dif_pos hW, dif_pos hW, dif_pos hV, Category.assoc, eqToHom_trans, ← Category.assoc,
          X.totalQuotientPresheaf_map_totalQuotientToFunctionField f hW]
      · rw [dif_neg hW]
        exact ((if_neg hW).symm.ndrec terminalIsTerminal).hom_ext _ _ }

/-- `𝒦_X` to the skyscraper sheaf: the universal property of sheafification (the skyscraper presheaf is a
sheaf). -/

noncomputable def AlgebraicGeometry.Scheme.rationalFunctionsSheafToSkyscraper
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] :
    open Classical in
    X.rationalFunctionsSheaf.val ⟶ skyscraperPresheaf (genericPoint X) X.functionField :=
  open Classical in
  CategoryTheory.sheafifyLift _ X.totalQuotientPresheafToSkyscraper
    (skyscraperPresheaf_isSheaf (genericPoint X) X.functionField)

/-- `𝒦_X(U) → K(X)` (`U` nonempty): restriction of a section of the sheaf of rational functions to the
generic point. -/

noncomputable def AlgebraicGeometry.Scheme.rationalSectionToFunctionField
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (U : X.Opens) [h : Nonempty U] :
    X.rationalFunctionsSheaf.val.obj (Opposite.op U) ⟶ X.functionField :=
  open Classical in
  X.rationalFunctionsSheafToSkyscraper.app (Opposite.op U) ≫
    eqToHom (if_pos (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h)))

/-- Compatibility with `O_X → 𝒦_X` and with the germ map. -/

theorem AlgebraicGeometry.Scheme.toRationalFunctionsSheaf_rationalSectionToFunctionField
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty U] :
    X.toRationalFunctionsSheaf.hom.app (Opposite.op U) ≫ X.rationalSectionToFunctionField U =
      X.germToFunctionField U := by
  classical
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hnat : X.toRationalFunctionsSheaf.hom ≫ X.rationalFunctionsSheafToSkyscraper =
      X.presheaf.toTotalQuotientPresheaf ≫ X.totalQuotientPresheafToSkyscraper :=
    (Category.assoc _ _ _).trans (congrArg (X.presheaf.toTotalQuotientPresheaf ≫ ·)
      (CategoryTheory.toSheafify_sheafifyLift _ _ _))
  have happ : X.toRationalFunctionsSheaf.hom.app (op U) ≫
      X.rationalFunctionsSheafToSkyscraper.app (op U) =
      X.presheaf.toTotalQuotientPresheaf.app (op U) ≫
        X.totalQuotientPresheafToSkyscraper.app (op U) :=
    congrArg (fun α => α.app (op U)) hnat
  have hsk : X.totalQuotientPresheafToSkyscraper.app (op U) =
      X.totalQuotientToFunctionField U hη ≫ eqToHom (if_pos hη).symm := dif_pos hη
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ eqToHom _) (happ.trans (congrArg (_ ≫ ·) hsk))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (X.presheaf.toTotalQuotientPresheaf.app (op U) ≫ ·)
    ((Category.assoc _ _ _).trans (congrArg (X.totalQuotientToFunctionField U hη ≫ ·)
      ((eqToHom_trans _ _).trans (eqToHom_refl _ rfl))))).trans ?_
  exact (congrArg (X.presheaf.toTotalQuotientPresheaf.app (op U) ≫ ·) (Category.comp_id _)).trans
    (X.toTotalQuotientPresheaf_app_comp_totalQuotientToFunctionField U hη)

/-- Compatibility with restriction. -/

theorem AlgebraicGeometry.Scheme.rationalSectionToFunctionField_res
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (U V : X.Opens) [Nonempty U]
    [Nonempty V] (hVU : V ≤ U) :
    X.rationalFunctionsSheaf.val.map (CategoryTheory.homOfLE hVU).op ≫ X.rationalSectionToFunctionField V =
      X.rationalSectionToFunctionField U := by
  classical
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hn := X.rationalFunctionsSheafToSkyscraper.naturality (homOfLE hVU).op
  have hsky : (skyscraperPresheaf (genericPoint X) X.functionField).map (homOfLE hVU).op =
      eqToHom _ := dif_pos hηV
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ eqToHom _) (hn.trans (congrArg (_ ≫ ·) hsky))).trans ?_
  exact (Category.assoc _ _ _).trans
    (congrArg (X.rationalFunctionsSheafToSkyscraper.app (op U) ≫ ·) (eqToHom_trans _ _))

open scoped nonZeroDivisors in

/-- The evaluation map `Q(O(V)) → K(X)` at the presheaf level is injective (the germ map is injective on an
integral scheme). -/

theorem AlgebraicGeometry.Scheme.totalQuotientToFunctionField_injective
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (V : X.Opens) (hV : genericPoint X ∈ V) :
    Function.Injective (X.totalQuotientToFunctionField V hV).hom := by
  change Function.Injective (IsLocalization.lift
      (M := (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (op V))
      (S := Localization
        ((X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (op V)))
      (g := (X.presheaf.germ V (genericPoint X) hV).hom)
      (fun s => X.isUnit_germ_genericPoint_of_mem V hV s))
  refine (IsLocalization.lift_injective_iff _).mpr fun a b => ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (IsLocalization.lift
      (M := (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (op V))
      (S := Localization
        ((X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (op V)))
      (g := (X.presheaf.germ V (genericPoint X) hV).hom)
      (fun s => X.isUnit_germ_genericPoint_of_mem V hV s)) h
    simpa only [IsLocalization.lift_eq] using this
  · exact congrArg _ (germ_injective_of_isIntegral X (genericPoint X) hV h)

/-- Evaluation at the generic point after the sheafification unit equals evaluation at the presheaf level. -/

theorem AlgebraicGeometry.Scheme.toSheafify_rationalSectionToFunctionField
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (V : X.Opens) [Nonempty V]
    (hV : genericPoint X ∈ V) :
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf).app (op V) ≫ X.rationalSectionToFunctionField V =
      X.totalQuotientToFunctionField V hV := by
  classical
  have hnat : CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf ≫ X.rationalFunctionsSheafToSkyscraper =
      X.totalQuotientPresheafToSkyscraper := CategoryTheory.toSheafify_sheafifyLift _ _ _
  have happ := congrArg (fun α => α.app (op V)) hnat
  have hsk : X.totalQuotientPresheafToSkyscraper.app (op V) =
      X.totalQuotientToFunctionField V hV ≫ eqToHom (if_pos hV).symm := dif_pos hV
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ eqToHom _) (happ.trans hsk)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (X.totalQuotientToFunctionField V hV ≫ ·)
    ((eqToHom_trans _ _).trans (eqToHom_refl _ rfl))).trans (Category.comp_id _))

/-- Injectivity half of Stacks 01X5: a section with value `0` comes locally from the presheaf, where it is
`0`, hence it is `0`. -/

theorem AlgebraicGeometry.Scheme.rationalSectionToFunctionField_injective
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective (X.rationalSectionToFunctionField U).hom := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hsieve := CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf)
    (U := op U) q
  have hloc : ∀ x : U, ∃ (V : X.Opens) (_ : x.1 ∈ V) (hVU : V ≤ U),
      (X.rationalFunctionsSheaf.val.map (homOfLE hVU).op).hom q = 0 := by
    intro x
    obtain ⟨V, i, ⟨p, hp⟩, hxV⟩ := hsieve x.1 x.2
    have : Nonempty V := ⟨⟨x.1, hxV⟩⟩
    have hηV : genericPoint X ∈ V :=
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x.1, trivial, hxV⟩
    have h1 : (X.rationalSectionToFunctionField V).hom
        ((X.rationalFunctionsSheaf.val.map i.op).hom q) = 0 :=
      (congrArg (fun φ => φ.hom q) (X.rationalSectionToFunctionField_res U V i.le)).trans hq
    have h2 : (X.totalQuotientToFunctionField V hηV).hom p = 0 :=
      ((congrArg (fun φ => φ.hom p) (X.toSheafify_rationalSectionToFunctionField V hηV)).symm.trans
        (congrArg (X.rationalSectionToFunctionField V).hom hp)).trans h1
    have h3 : p = 0 := X.totalQuotientToFunctionField_injective V hηV (h2.trans (map_zero _).symm)
    refine ⟨V, hxV, i.le, hp.symm.trans ?_⟩
    rw [h3]; exact map_zero _
  choose V hxV hVU hV0 using hloc
  apply X.rationalFunctionsSheaf.eq_of_locally_eq' V U (fun x => homOfLE (hVU x))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  intro x
  exact (hV0 x).trans (map_zero _).symm

open scoped nonZeroDivisors in

/-- Surjectivity half of Stacks 01X5: on affine opens `K(X) = Frac O(V)`, so `f = a/b` gives local sections;
by the injectivity half they agree on overlaps and glue. -/

theorem AlgebraicGeometry.Scheme.rationalSectionToFunctionField_surjective
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Surjective (X.rationalSectionToFunctionField U).hom := by
  intro f
  have hηmem : ∀ (V : X.Opens), Nonempty V → genericPoint X ∈ V := fun V hV =>
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hloc : ∀ x : U, ∃ (V : X.Opens) (hxV : x.1 ∈ V) (_ : V ≤ U)
      (q : X.rationalFunctionsSheaf.val.obj (op V)),
      (@rationalSectionToFunctionField X _ V ⟨⟨x.1, hxV⟩⟩).hom q = f := by
    intro x
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open x.2 U.isOpen
    have hne : Nonempty A := ⟨⟨x.1, hxA⟩⟩
    have hηA : genericPoint X ∈ A := hηmem A hne
    have := functionField_isFractionRing_of_isAffineOpen X A hA
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, A)) f
    have hbS : b ∈ (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj
        (op A) := by
      simp only [TopCat.Presheaf.submonoidPresheafOfStalk_obj, Submonoid.mem_iInf,
        Submonoid.mem_comap]
      intro y
      apply mem_nonZeroDivisors_of_ne_zero
      intro h0
      exact nonZeroDivisors.ne_zero hb
        (germ_injective_of_isIntegral X y.1 y.2 (h0.trans (map_zero _).symm))
    let p : X.presheaf.totalQuotientPresheaf.obj (op A) :=
      IsLocalization.mk'
        (M := (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (op A))
        (Localization
          ((X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (op A)))
        a ⟨b, hbS⟩
    refine ⟨A, hxA, hAU, (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf).app (op A) p, ?_⟩
    refine (congrArg (fun φ => φ.hom p)
      (X.toSheafify_rationalSectionToFunctionField A hηA)).trans ?_
    change IsLocalization.lift
      (M := (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (op A))
      (S := Localization
        ((X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (op A)))
      (g := (X.presheaf.germ A (genericPoint X) hηA).hom)
      (fun s => X.isUnit_germ_genericPoint_of_mem A hηA s) p = f
    rw [IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul]
    change _ = f * (X.presheaf.germ A (genericPoint X) hηA).hom b
    have hb0 : (X.presheaf.germ A (genericPoint X) hηA).hom b ≠ 0 := fun h0 =>
      nonZeroDivisors.ne_zero hb
        (germ_injective_of_isIntegral X (genericPoint X) hηA (h0.trans (map_zero _).symm))
    rw [← hab]
    exact (div_mul_cancel₀ _ hb0).symm
  choose V hxV hVU q hq using hloc
  have hne : ∀ x : U, Nonempty (V x) := fun x => ⟨⟨x.1, hxV x⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.rationalFunctionsSheaf.val V q := by
    intro x y
    have : Nonempty (V x) := hne x
    have : Nonempty (V y) := hne y
    have : Nonempty ((V x ⊓ V y : X.Opens)) :=
      ⟨⟨genericPoint X, hηmem _ (hne x), hηmem _ (hne y)⟩⟩
    apply X.rationalSectionToFunctionField_injective (V x ⊓ V y)
    have h1 := congrArg (fun φ => φ.hom (q x))
      (X.rationalSectionToFunctionField_res (V x) (V x ⊓ V y) inf_le_left)
    have h2 := congrArg (fun φ => φ.hom (q y))
      (X.rationalSectionToFunctionField_res (V y) (V x ⊓ V y) inf_le_right)
    exact (h1.trans (hq x)).trans ((h2.trans (hq y)).symm)
  obtain ⟨Q, hQ, -⟩ := X.rationalFunctionsSheaf.existsUnique_gluing' V U
    (fun x => homOfLE (hVU x)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩) q hcompat
  refine ⟨Q, ?_⟩
  obtain ⟨x₀⟩ := ‹Nonempty U›
  have : Nonempty (V x₀) := hne x₀
  have h1 := congrArg (fun φ => φ.hom Q) (X.rationalSectionToFunctionField_res U (V x₀) (hVU x₀))
  exact h1.symm.trans ((congrArg (X.rationalSectionToFunctionField (V x₀)).hom (hQ x₀)).trans (hq x₀))

/-- Stacks 01X5: on an integral scheme `𝒦_X(U) → K(X)` is bijective. -/

theorem AlgebraicGeometry.Scheme.rationalSectionToFunctionField_bijective
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Bijective (X.rationalSectionToFunctionField U).hom :=
  ⟨X.rationalSectionToFunctionField_injective U, X.rationalSectionToFunctionField_surjective U⟩

/-- The version for units: `𝒦_X^*(U) → K(X)^*`. -/

noncomputable def AlgebraicGeometry.Scheme.rationalUnitsSectionToFunctionField
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty U] :
    X.rationalFunctionsUnitsSheaf.val.obj (Opposite.op U) →* (X.functionField)ˣ :=
  Units.map ((X.rationalSectionToFunctionField U).hom :
    X.rationalFunctionsSheaf.val.obj (Opposite.op U) →* X.functionField)

/-- `𝒦^*(U) → K(X)^*` is compatible with restriction. -/
theorem AlgebraicGeometry.Scheme.rationalUnitsSectionToFunctionField_res
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (U W : X.Opens)
    [Nonempty U] [Nonempty W] (hWU : W ≤ U)
    (t : X.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    X.rationalUnitsSectionToFunctionField W
        (X.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op t) =
      X.rationalUnitsSectionToFunctionField U t :=
  Units.ext (congrArg (fun φ => φ.hom ((show (X.rationalFunctionsSheaf.val.obj (op U))ˣ from t) :
      X.rationalFunctionsSheaf.val.obj (op U))) (X.rationalSectionToFunctionField_res U W hWU))

/-- `𝒦^*(U) → K(X)^*` is injective. -/
theorem AlgebraicGeometry.Scheme.rationalUnitsSectionToFunctionField_injective
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective (X.rationalUnitsSectionToFunctionField U) := by
  intro t t' h
  exact Units.ext ((X.rationalSectionToFunctionField_bijective U).1 (congrArg Units.val h))

end
