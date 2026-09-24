import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateRestrictOfEqScale
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodFunctionsPullbackOfDegreePos
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodSectionEqZeroOfPreimageEqZero
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMinors
import MiyaokaMori.Paper.S3PositiveLine.Realization.ScalarOfSeedMinorsZeroGlobal
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.SectionIsZeroAtIso
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.XiCoefficientThickeningPullbackPos

/-! # Excluding generically scalar jets

If `ȷ` were generically scalar, its coefficients of each order would be `c_q·(s∘ρ)` with `c_q ∈ H^0(L^{-q})`;
since `d_L > 0` this forces `c_q = 0`, so the jet degenerates to the constant seed, contradicting the fact that the
tuple of normalized coefficients is nowhere zero (§3 of the paper, proof of Proposition 3.2).

The top level is assembled from five lemmas in their own modules —
`BasedJet.coneCoordinate_restrict_of_eq_scale` (coordinates of a scalar jet),
`jetNeighborhood.section_eq_zero_of_sectionPullbackAlong_preimage_eq_zero` (sections on the thickening vanishing
over a dense open vanish), `exists_smul_eq_of_sectionTensor_eq_of_nowhere_zero` (minors zero ⇒ global scalar),
`jetNeighborhood.appTop_eq_proj_zeroSection_of_degree_pos` (functions on the thickening are pulled back when
`deg L > 0`) and `xiCoefficientThickening_sectionPullbackAlong_of_pos`. The "quotient bundle
`Q ⊗ L^{-q}`" step of the paper is replaced by the equivalent statement that the
seed minors vanish, which needs no cokernel; the vanishing of `H^0(L^{-q})` enters through the fourth lemma.

`sectionPullbackAlong` is the one definition (its body is the adjunction unit) and
`AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback` its `Γ`-typed reducible abbrev: `unfold sectionPullbackAlong` does not produce
the `Γ`-typed spelling, so the proofs below use `simp only [sectionPullbackAlong_eq_pullback]` (to reach it) or
plain `unfold sectionPullbackAlong` (to reach the unit).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem sectionPullbackAlong_sub' {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) {M : Y.Modules}
    (s t : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong g (s - t) = sectionPullbackAlong g s - sectionPullbackAlong g t := by
  unfold sectionPullbackAlong
  exact map_sub _ s t

private theorem sectionTensor_smul_left' {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}
    (a : Γ(X, ⊤)) (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    sectionTensor (a • s : Γ(M, ⊤)) t
      = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • sectionTensor s t := by
  unfold sectionTensor
  have h1 : (1 : Γ(X, ⊤)) • t = t := one_smul _ t
  have h2 := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul (U := ⊤) a 1 s t
  rw [h1, mul_one] at h2
  exact h2

private theorem modules_iso_app_top_injective' {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules} (e : A ≅ B) :
    Function.Injective (fun s : (A.val.obj (Opposite.op ⊤) : Type u) => e.hom.app ⊤ s) := by
  intro s t h
  have hc : ∀ x : (A.val.obj (Opposite.op ⊤) : Type u), e.inv.app ⊤ (e.hom.app ⊤ x) = x := by
    intro x
    have hi := congrArg (fun ψ => (AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤) x) e.hom_inv_id
    exact hi
  have h' := congrArg (fun x => e.inv.app ⊤ x) h
  simp only [hc] at h'
  exact h'

private theorem isZeroAt_zero' {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} (x : X) :
    IsZeroAt (0 : (M.val.obj (Opposite.op ⊤) : Type u)) x := by
  change M.presheaf.germ ⊤ x trivial 0 ∈ _
  rw [map_zero]
  exact Submodule.zero_mem _

/-- **All positive-order coefficients of a jet that is scalar over a nonempty open set vanish** (when
`deg L > 0`). Hypothesis `hcoord`: on `W = p⁻¹U` (`U ≠ ∅`) the cone coordinates satisfy
`ι_W^*(P_ℓ) = a • ι_W^*(p^* ρ^* f_ℓ)` for one function `a ∈ Γ(W, O)` (this is what generic scalarity gives, via
`BasedJet.coneCoordinate_restrict_of_eq_scale`; the unit property and the normalisation of `a` are not needed).

Proof (§3 of the paper, proof of Proposition 3.2), with the
"quotient bundle" step replaced by the equivalent "seed minors" formulation:
1. The pulled-back seed tuple `ρ^* f_ℓ`, and hence `p^* ρ^* f_ℓ`, is nowhere zero on the thickening
   (`D.hcoord`: the homogeneous coordinates of `f` have no common zero; `not_isZeroAt_sectionPullbackAlong` twice).
2. The seed minors `P_i ⊗ p^*ρ^*f_j − P_j ⊗ p^*ρ^*f_i ∈ Γ(C̃_(κ), p^*A ⊗ p^*A)` vanish on `W`
   (`hcoord`, `pullbackTensorIso_sectionTensor`, `sectionTensor_comm_of_isLineBundle`), hence on all of `C̃_(κ)`
   (`jetNeighborhood.section_eq_zero_of_sectionPullbackAlong_preimage_eq_zero`: the thickening of an integral curve).
3. Minors zero + seed nowhere zero ⇒ `P_ℓ = b • p^* ρ^* f_ℓ` for a global `b ∈ Γ(C̃_(κ), O)`
   (`exists_smul_eq_of_sectionTensor_eq_of_nowhere_zero`).
4. `deg L > 0` ⇒ `b = p^*(σ₀^* b)` (`jetNeighborhood.appTop_eq_proj_zeroSection_of_degree_pos`: the components of
   `b` in `H^0(C̃, L^{-q})`, `q ≥ 1`, vanish by negativity of the degree), so `P_ℓ = p^*((σ₀^* b) • ρ^* f_ℓ)` is
   pulled back from the curve (`sectionPullbackAlong_smul`).
5. The positive-order coefficients of a pulled-back section vanish
   (`xiCoefficientThickening_sectionPullbackAlong_of_pos`). -/
theorem BasedJet.coefficient_eq_zero_of_coneCoordinate_restrict_eq_smul {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ) (hL : 0 < L.degree)
    (U : ρ.source.toScheme.Opens) (hU : (U : Set ρ.source.toScheme).Nonempty)
    (a : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤))
    (hcoord : ∀ ℓ,
      (sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι (BasedJet.coneCoordinate J ℓ) :
        (((AlgebraicGeometry.Scheme.Modules.pullback ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
            (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
              (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules)).val.obj
          (Opposite.op ⊤) : Type u))
        = (show ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
          sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι
            (sectionPullbackAlong (jetNeighborhood.proj L κ)
              (seedCoordPullback f ρ (D.coord ℓ))))
    (ℓ : Fin (X.embDim + 1)) (q : ℕ) (hq : 1 ≤ q) :
    BasedJet.coefficient J ℓ q = 0 := by
  -- notation
  let A : ρ.source.toScheme.Modules :=
    (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
  let s : Fin (X.embDim + 1) → (A.val.obj (Opposite.op ⊤) : Type u) :=
    fun ℓ => seedCoordPullback f ρ (D.coord ℓ)
  let ps : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj A).val.obj
        (Opposite.op ⊤) : Type u) :=
    fun ℓ => sectionPullbackAlong (jetNeighborhood.proj L κ) (s ℓ)
  let P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj A).val.obj
        (Opposite.op ⊤) : Type u) :=
    fun ℓ => BasedJet.coneCoordinate J ℓ
  -- (a) the pulled-back seed tuple is nowhere zero on the thickening
  have hs : ∀ z : (jetNeighborhood L κ).left, ∃ i, ¬ IsZeroAt (ps i) z := by
    intro z
    obtain ⟨hc, -⟩ := D.hcoord
    obtain ⟨i, hi⟩ := hc (ρ.hom.base ((jetNeighborhood.proj L κ).base z))
    refine ⟨i, ?_⟩
    apply not_isZeroAt_sectionPullbackAlong (jetNeighborhood.proj L κ) A (s i) z
    have key : ¬ IsZeroAt (sectionPullbackAlong ρ.hom (D.coord i)) ((jetNeighborhood.proj L κ).base z) :=
      not_isZeroAt_sectionPullbackAlong ρ.hom (seedLineBundle X.embedding f) (D.coord i) _ hi
    intro hz
    exact key ((isZeroAt_iso_iff
      ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).mapIso
        ((AlgebraicGeometry.Scheme.Modules.pullback f).mapIso
          (CategoryTheory.eqToIso (X.OX_toModules 1).symm)))
      (sectionPullbackAlong ρ.hom (D.coord i)) _).mp hz)
  -- (b) the seed minors of the cone coordinates vanish on the whole thickening
  have hminor : ∀ i j, sectionTensor (P i) (ps j) = sectionTensor (P j) (ps i) := by
    intro i j
    rw [← sub_eq_zero]
    apply jetNeighborhood.section_eq_zero_of_sectionPullbackAlong_preimage_eq_zero L κ _ U hU
    rw [sectionPullbackAlong_sub', sub_eq_zero]
    apply modules_iso_app_top_injective'
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι _ _)
    simp only [P, ps]
    rw [AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_sectionTensor,
      AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_sectionTensor, hcoord i, hcoord j]
    exact (sectionTensor_smul_left' _ _ _).trans
      ((congrArg (fun x => (show ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme.ringCatSheaf.obj.obj
          (Opposite.op ⊤) from a) • x) (AlgebraicGeometry.Scheme.Modules.sectionTensor_comm_of_isLineBundle _ _ _)).trans
        (sectionTensor_smul_left' _ _ _).symm)
  -- (c) a global scalar
  obtain ⟨b, hb⟩ := exists_smul_eq_of_sectionTensor_eq_of_nowhere_zero _ P ps hs hminor
  have hb' := jetNeighborhood.appTop_eq_proj_zeroSection_of_degree_pos L hL κ b
  have hP : P ℓ = sectionPullbackAlong (jetNeighborhood.proj L κ)
      ((show ρ.source.toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from
        (jetNeighborhood.zeroSection L κ).appTop b) • s ℓ) := by
    rw [sectionPullbackAlong_smul, ← hb', hb ℓ]
  -- (d) coefficients of a pulled-back section vanish in positive degree
  show xiCoefficientThickening L _ κ q (P ℓ) = 0
  rw [hP]
  exact xiCoefficientThickening_sectionPullbackAlong_of_pos L _ κ q hq _

/-- **Exclusion of generically scalar jets** (§3 of the paper, proof of Proposition 3.2).
If `J` were generically scalar, i.e. `ι_W ≫ J.hom = scale u (ι_W ≫ p ≫ ρ ≫ s)` over a nonempty open `U` of `C̃`,
then its cone coordinates on `W = p⁻¹U` would be `u • p^*ρ^*f_ℓ` (`BasedJet.coneCoordinate_restrict_of_eq_scale`),
so by `BasedJet.coefficient_eq_zero_of_coneCoordinate_restrict_eq_smul` (which uses `deg L > 0`) every coefficient
`c_{ℓ,q}`, `1 ≤ q ≤ κ`, would be `0`; but `hnz` says that at any point `y` of the (nonempty, connected) curve `C̃`
some `c_{ℓ,q}` with `1 ≤ q ≤ κ` does not vanish — contradiction, since the zero section vanishes everywhere. -/
theorem not_genericallyScalar_of_degree_pos {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
    (L : LineBundle ρ.source.toVariety) (hL : 0 < L.degree)
    (J : BasedJet f ρ L κ) (hnz : NormalizedTupleNowhereZero J) :
    ¬ J.IsGenericallyScalar := by
  rintro ⟨U, hU, u, -, hJ⟩
  have hne : Nonempty ρ.source.toScheme := ρ.source.connected.toNonempty
  obtain ⟨y⟩ := hne
  obtain ⟨ℓ, q, hq1, -, hzero⟩ := hnz y
  apply hzero
  rw [BasedJet.coefficient_eq_zero_of_coneCoordinate_restrict_eq_smul J hL U hU
    (u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤))
    (fun ℓ => BasedJet.coneCoordinate_restrict_of_eq_scale J U u hJ ℓ) ℓ q hq1]
  exact isZeroAt_zero' y

end
