import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenterAffineLeaf
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveSpaceIsIntegral

/-! # Stacks 02ND: the blowup of an integral scheme is integral

The blowup of an integral scheme along a nonzero quasi-coherent ideal sheaf is an integral scheme.

Source: Stacks 02ND; used for strict transforms.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData)

/-- The underlying section `Γ(X, U)` of an element of the `m`-th Rees piece `Γ(U, Iᵐ) ⊆ Γ(X, U)`. -/
def reesPieceVal (U : X.Opens) (m : ℕ) (a : I.reesAlgebra.sectionsPiece U m) : Γ(X, U) := a.1

theorem reesPieceVal_zero (U : X.Opens) (m : ℕ) : I.reesPieceVal U m 0 = 0 := rfl

theorem reesPieceVal_add (U : X.Opens) (m : ℕ) (a b : I.reesAlgebra.sectionsPiece U m) :
    I.reesPieceVal U m (a + b) = I.reesPieceVal U m a + I.reesPieceVal U m b := rfl

theorem reesPieceVal_injective (U : X.Opens) (m : ℕ) : Function.Injective (I.reesPieceVal U m) :=
  fun _ _ h => Subtype.ext h

/-- The unit of the Rees algebra on sections is `1 ∈ Γ(X, U)`. -/
theorem reesPieceVal_sectionsGOne (U : X.Opens) :
    I.reesPieceVal U 0 (I.reesAlgebra.sectionsGOne U) = 1 := by
  with_unfolding_all rfl

/-- The graded multiplication of the Rees algebra on sections is the multiplication of `Γ(X, U)`
(`coe_reesAlgebra_sectionsGMul`). -/
theorem reesPieceVal_sectionsGMul (U : X.Opens) (m n : ℕ)
    (a : I.reesAlgebra.sectionsPiece U m) (b : I.reesAlgebra.sectionsPiece U n) :
    I.reesPieceVal U (m + n) (I.reesAlgebra.sectionsGMul U a b) =
      I.reesPieceVal U m a * I.reesPieceVal U n b :=
  I.coe_reesAlgebra_sectionsGMul U m n a b

/-- The additive map `Γ(U, Iᵐ) → Γ(X, U)[T]`, `a ↦ a Tᵐ`. -/
def reesPieceToPolynomial (U : X.Opens) (m : ℕ) :
    I.reesAlgebra.sectionsPiece U m →+ Polynomial Γ(X, U) where
  toFun a := Polynomial.monomial m (I.reesPieceVal U m a)
  map_zero' := by rw [reesPieceVal_zero, map_zero]
  map_add' a b := by rw [reesPieceVal_add, map_add]

/-- The ring map `S(U) = ⊕ₘ Γ(U, Iᵐ) → Γ(X, U)[T]`, `(aₘ)ₘ ↦ Σ aₘ Tᵐ`. -/
def reesSectionsToPolynomial (U : X.Opens) :
    (⨁ m, I.reesAlgebra.sectionsPiece U m) →+* Polynomial Γ(X, U) :=
  DirectSum.toSemiring (I.reesPieceToPolynomial U)
    (by
      show Polynomial.monomial 0 (I.reesPieceVal U 0 (I.reesAlgebra.sectionsGOne U)) = 1
      rw [I.reesPieceVal_sectionsGOne U, Polynomial.monomial_zero_one])
    (by
      intro i j a b
      show Polynomial.monomial (i + j) (I.reesPieceVal U (i + j) (I.reesAlgebra.sectionsGMul U a b)) =
        Polynomial.monomial i (I.reesPieceVal U i a) * Polynomial.monomial j (I.reesPieceVal U j b)
      rw [I.reesPieceVal_sectionsGMul U i j a b, Polynomial.monomial_mul_monomial])

theorem coeff_reesSectionsToPolynomial (U : X.Opens) (x : ⨁ m, I.reesAlgebra.sectionsPiece U m)
    (n : ℕ) :
    (I.reesSectionsToPolynomial U x).coeff n = I.reesPieceVal U n (x n) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, Polynomial.coeff_zero, DirectSum.zero_apply, reesPieceVal_zero]
  | of i a =>
    rw [reesSectionsToPolynomial, DirectSum.toSemiring_of]
    show (Polynomial.monomial i (I.reesPieceVal U i a)).coeff n = _
    rw [Polynomial.coeff_monomial]
    by_cases h : i = n
    · subst h
      rw [DirectSum.of_eq_same, if_pos rfl]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), if_neg h, reesPieceVal_zero]
  | add x y hx hy =>
    rw [map_add, Polynomial.coeff_add, hx, hy, DirectSum.add_apply, reesPieceVal_add]

theorem reesSectionsToPolynomial_injective (U : X.Opens) :
    Function.Injective (I.reesSectionsToPolynomial U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  ext n
  have h := I.coeff_reesSectionsToPolynomial U x n
  rw [hx, Polynomial.coeff_zero] at h
  rw [DirectSum.zero_apply]
  exact I.reesPieceVal_injective U n (h.symm.trans (I.reesPieceVal_zero U n).symm)

/-- If `Γ(X, U)` is a domain, so is the Rees sections ring `⊕ₘ Γ(U, Iᵐ)` (it embeds into
`Γ(X, U)[T]`). -/
theorem reesAlgebra_sectionsRing_isDomain (U : X.Opens) [IsDomain Γ(X, U)] :
    IsDomain (I.reesAlgebra.sectionsRing U) :=
  Function.Injective.isDomain (I.reesSectionsToPolynomial U) (I.reesSectionsToPolynomial_injective U)

/-- A section `a ∈ I(U)` on an affine open `U` lies in `Γ(U, I¹)`. -/
theorem mem_powSubmodule_one_of_mem (U : X.affineOpens) (a : Γ(X, U.1)) (ha : a ∈ I.ideal U) :
    a ∈ (I.powSubmodule 1).obj (op U.1) := by
  intro V hV
  rw [pow_one, ← I.map_ideal (U := V) (V := U) hV]
  exact Ideal.mem_map_of_mem _ ha

theorem exists_degreeOne_ne_zero (U : X.affineOpens) (hU : I.ideal U ≠ ⊥) :
    ∃ f : I.reesAlgebra.sectionsRing U.1, f ∈ I.reesAlgebra.sectionsGrading U.1 1 ∧ f ≠ 0 := by
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp hU
  have ha1 := I.mem_powSubmodule_one_of_mem U a ha
  refine ⟨DirectSum.of (I.reesAlgebra.sectionsPiece U.1) 1 ⟨a, ha1⟩, ⟨_, rfl⟩, ?_⟩
  intro h
  have h2 : (DirectSum.of (I.reesAlgebra.sectionsPiece U.1) 1 ⟨a, ha1⟩) 1 = ⟨a, ha1⟩ :=
    DirectSum.of_eq_same 1 _
  have h4 : (DirectSum.of (I.reesAlgebra.sectionsPiece U.1) 1 ⟨a, ha1⟩) 1 =
      (0 : ⨁ m, I.reesAlgebra.sectionsPiece U.1 m) 1 :=
    congrArg (fun z : ⨁ m, I.reesAlgebra.sectionsPiece U.1 m => z 1) h
  exact ha0 (congrArg (I.reesPieceVal U.1 1) (h2.symm.trans h4))

/-- **Chart of the blowup is integral**: on a nonempty affine open `U` of an integral scheme `X` with
`I(U) ≠ 0`, `Proj S(U)` (with `S = ⊕ Iⁿ`) is integral. -/
theorem proj_reesAlgebra_grading_isIntegral [AlgebraicGeometry.IsIntegral X]
    (U : X.AffineZariskiSite) (hne : (U.toOpens : Set X).Nonempty)
    (hU : I.ideal ⟨U.toOpens, U.2⟩ ≠ ⊥) :
    AlgebraicGeometry.IsIntegral
      (AlgebraicGeometry.Proj (I.reesAlgebra.toGradedAffineAlgebra.grading U)) := by
  have : Nonempty U.toOpens := ⟨⟨hne.some, hne.some_mem⟩⟩
  have : IsDomain Γ(X, U.toOpens) := IsIntegral.component_integral U.toOpens
  have : IsDomain (I.reesAlgebra.toGradedAffineAlgebra.ring.obj (op U)) :=
    I.reesAlgebra_sectionsRing_isDomain U.toOpens
  obtain ⟨f, hf, hf0⟩ := I.exists_degreeOne_ne_zero ⟨U.toOpens, U.2⟩ hU
  exact AlgebraicGeometry.Proj.isIntegral_of_isDomain _ ⟨1, f, Nat.one_pos, hf, hf0⟩

/-- On an integral scheme, `I ≠ ⊥` forces `I(U) ≠ 0` on **every** nonempty affine open `U`:
pick affine `V` with `I(V) ∋ s ≠ 0`; `V` is nonempty (`D(s) ≠ ∅` on a reduced scheme); `U ∩ V ≠ ∅`
(irreducibility) contains an affine `W = D_U(f) = D_V(g)`; `I(W) = I(V)·O(W) ∋ s|_W ≠ 0`
(restrictions are injective on an integral scheme), and `I(W) = I(U)·O(W)`, so `I(U) ≠ 0`. -/
theorem ideal_ne_bot_of_ne_bot [AlgebraicGeometry.IsIntegral X] (hI : I ≠ ⊥) (U : X.affineOpens)
    (hne : (U.1 : Set X).Nonempty) : I.ideal U ≠ ⊥ := by
  have hV : ∃ V : X.affineOpens, I.ideal V ≠ ⊥ := by
    by_contra h
    exact hI (le_antisymm (le_def.mpr fun V =>
      le_of_eq_of_le (Classical.not_not.mp (not_exists.mp h V)) bot_le) bot_le)
  obtain ⟨V, hV⟩ := hV
  obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).mp hV
  have hbs : X.basicOpen s ≠ ⊥ := fun h => hs0 ((AlgebraicGeometry.basicOpen_eq_bot_iff s).mp h)
  obtain ⟨x₀, hx₀⟩ := (Opens.ne_bot_iff_nonempty _).mp hbs
  have hx₀V : x₀ ∈ V.1 := X.basicOpen_le s hx₀
  obtain ⟨x, hxU, hxV⟩ :=
    nonempty_preirreducible_inter U.1.isOpen V.1.isOpen hne ⟨x₀, hx₀V⟩
  obtain ⟨f, g, hfg, hxf⟩ := AlgebraicGeometry.exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩
  have hWU : X.affineBasicOpen f ≤ U := X.basicOpen_le f
  have hWV : X.affineBasicOpen f ≤ V := by
    show X.basicOpen f ≤ V.1
    rw [hfg]
    exact X.basicOpen_le g
  have : Nonempty (X.affineBasicOpen f).1 := ⟨⟨x, hxf⟩⟩
  intro hU
  have h1 := I.map_ideal hWU
  have h2 := I.map_ideal hWV
  rw [hU, Ideal.map_bot] at h1
  have hsW : (X.presheaf.map (homOfLE hWV).op).hom s ∈ I.ideal (X.affineBasicOpen f) :=
    h2 ▸ Ideal.mem_map_of_mem _ hs
  rw [← h1, Ideal.mem_bot] at hsW
  exact hs0 ((map_eq_zero_iff _
    (AlgebraicGeometry.map_injective_of_isIntegral (X := X) (homOfLE hWV))).mp hsW)

/-- On an integral scheme with `I ≠ ⊥`, every nonempty affine open `U` contains a point outside
the support `V(I)`: take `0 ≠ f ∈ I(U)`; `D(f) ≠ ∅` (reduced) and `D(f) ∩ V(I) = ∅`. -/
theorem exists_mem_notMem_support [AlgebraicGeometry.IsIntegral X] (hI : I ≠ ⊥)
    (U : X.affineOpens) (hne : (U.1 : Set X).Nonempty) :
    ∃ x ∈ U.1, x ∉ I.support := by
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).mp (I.ideal_ne_bot_of_ne_bot hI U hne)
  have hbf : X.basicOpen f ≠ ⊥ := fun h => hf0 ((AlgebraicGeometry.basicOpen_eq_bot_iff f).mp h)
  obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).mp hbf
  have hxU : x ∈ U.1 := X.basicOpen_le f hx
  refine ⟨x, hxU, fun hxS => ?_⟩
  rw [I.mem_support_iff_of_mem hxU, X.mem_zeroLocus_iff] at hxS
  exact hxS f hf hx

/-- Every point `p ∉ V(I)` is in the image of the blowup `b : X' → X`: choose an affine open
`A ∋ p` disjoint from `V(I)`; then `I(A) = ⊤`, so the chart structure map `Proj S(A) → A` is an
isomorphism (`isIso_reesAlgebra_projToOpen_of_ideal_eq_top`), and the chart `Proj S(A) → X'`
composed with `b` is that map followed by `A ↪ X` (`projChart_hom`). -/
theorem exists_blowup_hom_eq_of_notMem_support (p : X) (hp : p ∉ I.support) :
    ∃ z : (AlgebraicGeometry.Scheme.blowup I).left, (AlgebraicGeometry.Scheme.blowup I).hom z = p := by
  have hopen : IsOpen ((I.support : Set X)ᶜ) := I.support.isClosed.isOpen_compl
  obtain ⟨A, hA, hpA, hAle⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := ⟨_, hopen⟩)
      (show p ∈ (I.support : Set X)ᶜ from hp)
  let A' : X.AffineZariskiSite := ⟨A, hA⟩
  have hdisj : Disjoint (A : Set X) (I.support : Set X) :=
    Set.disjoint_left.mpr fun x hxA hxS => (hAle hxA : x ∈ (I.support : Set X)ᶜ) hxS
  have htop : I.ideal ⟨A'.toOpens, A'.2⟩ = ⊤ := I.ideal_eq_top_of_disjoint_support ⟨A, hA⟩ hdisj
  have := I.isIso_reesAlgebra_projToOpen_of_ideal_eq_top A' htop
  obtain ⟨y, hy⟩ :=
    (I.reesAlgebra.toGradedAffineAlgebra.projToOpen A').homeomorph.surjective ⟨p, hpA⟩
  refine ⟨I.reesAlgebra.toGradedAffineAlgebra.projChart A' y, ?_⟩
  show I.reesAlgebra.toGradedAffineAlgebra.relativeProj.hom
    (I.reesAlgebra.toGradedAffineAlgebra.projChart A' y) = p
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, GradedAffineAlgebra.projChart_hom,
    AlgebraicGeometry.Scheme.Hom.comp_apply]
  rw [AlgebraicGeometry.Scheme.Hom.homeomorph_apply] at hy
  rw [hy]
  rfl

end AlgebraicGeometry.Scheme.IdealSheafData

/-- **Stacks 02ND**: the blowup `X' = Bl_I X → X` of an integral scheme `X` along a nonzero
quasi-coherent ideal sheaf `I` is integral.

Proof (via the relative-Proj charts rather than the affine blowup algebras):
`X' = Proj_X (⊕ₙ Iⁿ)` is covered by the open charts `Proj S(A)`, `A` affine open in `X`, with
`S(A) = ⊕ₙ Γ(A, Iⁿ)` (`GradedAffineAlgebra.projChart`, `exists_projChart_mem`).
1. For nonempty affine `A`: `Γ(X, A)` is a domain and `I(A) ≠ 0` (`ideal_ne_bot_of_ne_bot`), so `S(A)`
   is a domain (it embeds into `Γ(X, A)[T]`, `reesSectionsToPolynomial_injective`) with a nonzero
   element of degree one (`exists_degreeOne_ne_zero`), hence `Proj S(A)` is integral
   (`Proj.isIntegral_of_isDomain`, `proj_reesAlgebra_grading_isIntegral`).
2. Charts over empty `A` contain no point (`b(chart point) ∈ A`), so the charts over nonempty `A`
   form an open cover of `X'` by reduced schemes: `X'` is reduced (`IsReduced.of_openCover`).
3. Any two chart images `P_A, P_B` (`A, B` nonempty affine) meet: `A ∩ B` contains a nonempty affine
   `D(f)`, which contains a point `p ∉ V(I)` (`exists_mem_notMem_support`), and `p = b(z)` for some
   `z ∈ X'` (`exists_blowup_hom_eq_of_notMem_support`), so `z ∈ P_A ∩ P_B`.
4. Irreducibility: given nonempty opens `W₁ ∋ x₁ ∈ P_A`, `W₂ ∋ x₂ ∈ P_B`, irreducibility of `P_A`
   gives a point of `W₁ ∩ P_B`, then irreducibility of `P_B` gives a point of `W₁ ∩ W₂`.
   `X'` is nonempty by 3, hence irreducible; with 2, integral.

Edge cases: `I = ⊤` (empty centre) is allowed — `X' ≅ X`; `I = ⊥` is excluded by `hI` (then `X' = ∅`). -/
theorem AlgebraicGeometry.Scheme.blowup_isIntegral {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Scheme.blowup I).left := by
  set T := I.reesAlgebra.toGradedAffineAlgebra with hT
  change AlgebraicGeometry.IsIntegral T.relativeProj.left
  have hchart_ne : ∀ (A : X.AffineZariskiSite) (y : AlgebraicGeometry.Proj (T.grading A)),
      (A.toOpens : Set X).Nonempty :=
    fun A y => ⟨(T.projToOpen A y).1, (T.projToOpen A y).2⟩
  have hint : ∀ A : X.AffineZariskiSite, (A.toOpens : Set X).Nonempty →
      AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Proj (T.grading A)) :=
    fun A hne => I.proj_reesAlgebra_grading_isIntegral A hne
      (I.ideal_ne_bot_of_ne_bot hI ⟨A.toOpens, A.2⟩ hne)
  -- reducedness via the open cover by charts over nonempty affine opens
  let J := {A : X.AffineZariskiSite // (A.toOpens : Set X).Nonempty}
  let 𝒰 : T.relativeProj.left.OpenCover :=
    AlgebraicGeometry.Scheme.Cover.mkOfCovers J (fun A => AlgebraicGeometry.Proj (T.grading A.1))
      (fun A => T.projChart A.1)
      (fun x => by
        obtain ⟨A, y, hy⟩ := T.exists_projChart_mem x
        exact ⟨⟨A, hchart_ne A y⟩, y, hy⟩)
  have : ∀ i, AlgebraicGeometry.IsReduced (𝒰.X i) := fun i => by
    have := hint i.1 i.2
    show AlgebraicGeometry.IsReduced (AlgebraicGeometry.Proj (T.grading i.1))
    infer_instance
  have hred : AlgebraicGeometry.IsReduced T.relativeProj.left :=
    AlgebraicGeometry.IsReduced.of_openCover _ 𝒰
  -- chart images
  have hP_irr : ∀ A : X.AffineZariskiSite, (A.toOpens : Set X).Nonempty →
      IsIrreducible (Set.range (T.projChart A)) := fun A hne => by
    have := hint A hne
    have h := (IrreducibleSpace.isIrreducible_univ (AlgebraicGeometry.Proj (T.grading A))).image
      (T.projChart A) (T.projChart A).continuous.continuousOn
    rwa [Set.image_univ] at h
  have hP_open : ∀ A : X.AffineZariskiSite, IsOpen (Set.range (T.projChart A)) :=
    fun A => (T.projChart A).isOpenEmbedding.isOpen_range
  have hP_mem : ∀ (A : X.AffineZariskiSite) (z : T.relativeProj.left),
      T.relativeProj.hom z ∈ A.toOpens → z ∈ Set.range (T.projChart A) := fun A z hz => by
    have hz' : z ∈ T.relativeProj.hom ⁻¹ᵁ A.toOpens := hz
    rw [T.proj_preimage_eq_opensRange A] at hz'
    exact hz'
  have hPP : ∀ A B : X.AffineZariskiSite, (A.toOpens : Set X).Nonempty →
      (B.toOpens : Set X).Nonempty →
      (Set.range (T.projChart A) ∩ Set.range (T.projChart B)).Nonempty := fun A B hA hB => by
    obtain ⟨x, hxA, hxB⟩ :=
      nonempty_preirreducible_inter A.toOpens.isOpen B.toOpens.isOpen hA hB
    obtain ⟨f, g, hfg, hxf⟩ :=
      AlgebraicGeometry.exists_basicOpen_le_affine_inter A.2 B.2 x ⟨hxA, hxB⟩
    obtain ⟨p, hpf, hpS⟩ := I.exists_mem_notMem_support hI (X.affineBasicOpen f) ⟨x, hxf⟩
    obtain ⟨z, hz⟩ := I.exists_blowup_hom_eq_of_notMem_support p hpS
    have hz' : T.relativeProj.hom z = p := hz
    refine ⟨z, hP_mem A z ?_, hP_mem B z ?_⟩
    · rw [hz']
      exact X.basicOpen_le f hpf
    · rw [hz']
      have hpg : p ∈ X.basicOpen g := hfg ▸ hpf
      exact X.basicOpen_le g hpg
  -- nonempty
  have hne' : Nonempty T.relativeProj.left := by
    obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
    obtain ⟨A, hA, hx₀A, -⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := ⊤) (show x₀ ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨p, -, hpS⟩ := I.exists_mem_notMem_support hI ⟨A, hA⟩ ⟨x₀, hx₀A⟩
    obtain ⟨z, -⟩ := I.exists_blowup_hom_eq_of_notMem_support p hpS
    exact ⟨z⟩
  -- irreducible
  have hpre : PreirreducibleSpace T.relativeProj.left := by
    refine PreirreducibleSpace.of_forall_nonempty_inter ?_
    intro W₁ W₂ hW₁ hW₂ hW₁ne hW₂ne
    obtain ⟨x₁, hx₁⟩ := hW₁ne
    obtain ⟨x₂, hx₂⟩ := hW₂ne
    obtain ⟨A, y₁, rfl⟩ := T.exists_projChart_mem x₁
    obtain ⟨B, y₂, rfl⟩ := T.exists_projChart_mem x₂
    have hA := hchart_ne A y₁
    have hB := hchart_ne B y₂
    obtain ⟨w, -, hwW₁, hwB⟩ := (hP_irr A hA).2 W₁ (Set.range (T.projChart B)) hW₁ (hP_open B)
      ⟨_, ⟨y₁, rfl⟩, hx₁⟩ (hPP A B hA hB)
    obtain ⟨v, -, hv⟩ := (hP_irr B hB).2 W₁ W₂ hW₁ hW₂ ⟨w, hwB, hwW₁⟩ ⟨_, ⟨y₂, rfl⟩, hx₂⟩
    exact ⟨v, hv⟩
  have : IrreducibleSpace T.relativeProj.left := { hpre with toNonempty := hne' }
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

end
