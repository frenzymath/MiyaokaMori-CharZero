import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesCoevaluation
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionsRingIsDomain

/-! # The total space of a vector bundle on an integral scheme is integral

Statement: if `X` is an integral scheme and `V` a locally free sheaf of finite type on `X`, then the total space
`Tot(V) = Spec_X Sym(V^∨)` is an integral scheme.

Proof:
1. Locally: take an affine open cover `{W_i}` of `X` with `V|_{W_i} ≅ O^{⊕r_i}` (`IsLocallyFree` + `IsFiniteType` give
   finite rank). The relative Spec commutes with restriction to the base (`affineIso` of the relative Spec):
   `p⁻¹(W_i) ≅ Spec Γ(W_i, Sym(V^∨)) ≅ Spec O(W_i)[t_1,…,t_{r_i}]`. `O(W_i)` is a domain (`X` integral, `W_i` a nonempty
   affine open) and so is the polynomial ring, so `p⁻¹(W_i)` is integral, in particular reduced and irreducible.
   (`symGradedAlgebra` is the trivial algebra when `V^∨` is not quasi-coherent; for `V` locally free of finite type
   `V^∨` is quasi-coherent, and even in the trivial branch `Tot(V) ≅ X` would be integral.)
2. Reducedness is local, so `Tot(V)` is reduced (`isReduced_of_isOpenImmersion` / `IsReduced.of_openCover`).
3. Irreducibility: `X` is nonempty, so `Tot(V)` is nonempty (zero section); `X` irreducible ⇒ `W_i ∩ W_j ≠ ∅` ⇒
   `p⁻¹(W_i) ∩ p⁻¹(W_j) = p⁻¹(W_i ∩ W_j) ≠ ∅` (`p` has a section, hence is surjective). A space covered by pairwise
   intersecting irreducible opens is irreducible.
4. Reduced + irreducible ⇒ integral (`isIntegral_of_irreducibleSpace_of_isReduced`).

Reference: near Stacks 01M2 (the total space of a vector bundle is locally `A^r_W`).

Steps 2–4 (gluing: reduced + irreducible ⇒ integral) are `totalSpace_isIntegral`; the ring-level content of step 1
(`Γ(U, Sym(V^∨))` is a domain on a trivializing affine open) is `totalSpace_sectionsRing_isDomain_of_le_locallyFreeData`
(`TotalSpaceSectionsRingIsDomain`). The cover consists of the preimages `p⁻¹U` of the nonempty affine opens `U` contained
in some trivializing open `X i` of `locallyFreeData V` (`PreirreducibleSpace.of_isOpenCover` requires pairwise
intersections, so empty opens must be excluded).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.totalSpace_isIntegral {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Scheme.totalSpace V).left := by
  classical
  -- notation
  set A : X.QCAlgebra := (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual V)).total with hA
  let p : (AlgebraicGeometry.Scheme.totalSpace V).left ⟶ X := (AlgebraicGeometry.Scheme.totalSpace V).hom
  let q := AlgebraicGeometry.Scheme.Modules.locallyFreeData V
  -- the zero section gives the surjectivity of p
  have hsec : ∀ z : X, p.base ((AlgebraicGeometry.Scheme.zeroSection V).base z) = z := by
    intro z
    have h := congrArg (fun f : X ⟶ X => f.base z) (AlgebraicGeometry.Scheme.zeroSection_comp V)
    simpa using h
  -- index: the nonempty affine opens contained in some trivializing open q.X i
  let ι : Type u := { U : X.affineOpens // (U.1 : Set X).Nonempty ∧ ∃ i, U.1 ≤ q.X i }
  let W : ι → (AlgebraicGeometry.Scheme.totalSpace V).left.Opens := fun U => p ⁻¹ᵁ U.1.1
  -- the cover
  have hqcov : TopologicalSpace.IsOpenCover q.X :=
    (_root_.Opens.coversTop_iff _ q.X).mp q.coversTop
  have hW : TopologicalSpace.IsOpenCover W := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro t _
    rw [TopologicalSpace.Opens.mem_iSup]
    have ht : p.base t ∈ ⨆ i, q.X i := hqcov.symm ▸ show p.base t ∈ (⊤ : X.Opens) by trivial
    rw [TopologicalSpace.Opens.mem_iSup] at ht
    obtain ⟨i, hi⟩ := ht
    obtain ⟨U, hUaff, htU, hUX⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := p.base t) (U := q.X i) hi
    exact ⟨⟨⟨U, hUaff⟩, ⟨p.base t, htU⟩, i, hUX⟩, htU⟩
  -- each piece p⁻¹U ≅ Spec A(U) is integral
  have hint : ∀ U : ι, AlgebraicGeometry.IsIntegral (W U).toScheme := by
    intro U
    obtain ⟨hne, i, hUX⟩ := U.2
    have : Nonempty U.1.1 := hne.to_subtype
    have : IsDomain (A.sectionsRing U.1.1) :=
      AlgebraicGeometry.Scheme.totalSpace_sectionsRing_isDomain_of_le_locallyFreeData V U.1 i hUX
    have : AlgebraicGeometry.IsIntegral
        (AlgebraicGeometry.Spec (CommRingCat.of (A.sectionsRing U.1.1))) := inferInstance
    let e : (W U).toScheme ≅ AlgebraicGeometry.Spec (CommRingCat.of (A.sectionsRing U.1.1)) :=
      AlgebraicGeometry.Scheme.relativeSpec.affineIso A U.1
    have : Nonempty (W U).toScheme := ⟨e.inv.base (Nonempty.some inferInstance)⟩
    exact AlgebraicGeometry.isIntegral_of_isOpenImmersion e.hom
  -- reduced
  have hred : AlgebraicGeometry.IsReduced (AlgebraicGeometry.Scheme.totalSpace V).left :=
    @AlgebraicGeometry.IsReduced.of_openCover _
      ((AlgebraicGeometry.Scheme.totalSpace V).left.openCoverOfIsOpenCover W hW)
      (fun U => by
        have := hint U
        exact inferInstanceAs (AlgebraicGeometry.IsReduced (W U).toScheme))
  -- irreducible: pairwise intersections
  have hn : Pairwise (Function.onFun (fun a b => ¬ Disjoint a b) W) := by
    intro U U' _
    intro hdisj
    obtain ⟨x, hx⟩ := U.2.1
    obtain ⟨y, hy⟩ := U'.2.1
    obtain ⟨z, -, hzU, hzU'⟩ :=
      (PreirreducibleSpace.isPreirreducible_univ (X := X)) U.1.1 U'.1.1 U.1.1.isOpen U'.1.1.isOpen
        ⟨x, trivial, hx⟩ ⟨y, trivial, hy⟩
    have hz : (AlgebraicGeometry.Scheme.zeroSection V).base z ∈ W U ⊓ W U' := by
      refine ⟨?_, ?_⟩
      · show p.base _ ∈ U.1.1
        rw [hsec]; exact hzU
      · show p.base _ ∈ U'.1.1
        rw [hsec]; exact hzU'
    exact hdisj.le_bot hz
  have hpre : PreirreducibleSpace (AlgebraicGeometry.Scheme.totalSpace V).left :=
    PreirreducibleSpace.of_isOpenCover hn hW fun U => by
      have := hint U
      exact inferInstanceAs (PreirreducibleSpace (W U).toScheme)
  have hne : Nonempty (AlgebraicGeometry.Scheme.totalSpace V).left :=
    ⟨(AlgebraicGeometry.Scheme.zeroSection V).base (Nonempty.some inferInstance)⟩
  have : IrreducibleSpace (AlgebraicGeometry.Scheme.totalSpace V).left := ⟨hne⟩
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

end
