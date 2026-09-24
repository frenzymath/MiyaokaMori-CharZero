import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperIntersectionEqChow
import MiyaokaMori.AlgebraicGeometry.Cohomology.SnapperPolynomial
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperIntersectionEqCoeff

/-! # The top self-intersection from the Euler characteristic

The coefficient of `p^{dim X}` in the polynomial `χ(X, L^{⊗p})` in `p`, multiplied by `(dim X)!`, equals
the top self-intersection `(L^{dim X})` (Lazarsfeld, Positivity in Algebraic Geometry I, 1.1.24; used in
the proof of Proposition 2.4 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory
noncomputable section

/-- The contraction `L ⊗ L^∨ ≅ O_X` of a line bundle. -/
private noncomputable def rawContraction {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    L ⊗ AlgebraicGeometry.Scheme.Modules.dual L ≅ 𝟙_ X.Modules :=
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L
      (AlgebraicGeometry.Scheme.Modules.dual L)).symm ≪≫
    -- the canonical evaluation map `L ⊗ L^∨ → O_X`; it is an isomorphism by `isIso_tensorDualEval`
    -- (Stacks 01CT), so no arbitrary choice of isomorphism is involved
    (haveI := SheafOfModules.IsLineBundle.isIso_tensorDualEval L
     CategoryTheory.asIso
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L (AlgebraicGeometry.Scheme.Modules.dual L)).hom ≫
        (β_ L (AlgebraicGeometry.Scheme.Modules.dual L)).hom ≫
        AlgebraicGeometry.Scheme.Modules.internalHomEval L (SheafOfModules.unit X.ringCatSheaf))) ≪≫
    CategoryTheory.eqToIso
      (show (SheafOfModules.unit X.ringCatSheaf) = 𝟙_ X.Modules by
        with_unfolding_all rfl)

/-- `L ^ p ≅ mzpow L p`: the integer power of a line bundle in its two spellings. -/
private noncomputable def rawZpowIsoMzpow {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (p : ℤ) :
    L ^ p ≅ AlgebraicGeometry.Scheme.Modules.mzpow L
      (AlgebraicGeometry.Scheme.Modules.dual L) p := by
  cases p with
  | ofNat n =>
      change AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n ≅
        AlgebraicGeometry.Scheme.Modules.mpow L n
      exact AlgebraicGeometry.Scheme.Modules.tensorPowerIsoMpow L n
  | negSucc n =>
      change AlgebraicGeometry.Scheme.Modules.moduleNegativePower L (n + 1) ≅
        AlgebraicGeometry.Scheme.Modules.mpow
          (AlgebraicGeometry.Scheme.Modules.dual L) (n + 1)
      exact AlgebraicGeometry.Scheme.Modules.tensorPowerIsoMpow
        (AlgebraicGeometry.Scheme.Modules.dual L) (n + 1)

/-- `L ^ (p + q) ≅ L ^ p ⊗ L ^ q`. -/
private noncomputable def rawZpowAddIso {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (p q : ℤ) :
    L ^ (p + q) ≅ AlgebraicGeometry.Scheme.Modules.tensor (L ^ p) (L ^ q) :=
  rawZpowIsoMzpow L (p + q) ≪≫
    AlgebraicGeometry.Scheme.Modules.mzpowAdd
      (rawContraction L) p q ≪≫
    (CategoryTheory.MonoidalCategory.tensorIso
      (rawZpowIsoMzpow L p) (rawZpowIsoMzpow L q)).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      (L ^ p) (L ^ q)).symm

/-- An isomorphism `A ≅ A'` induces `A ⊗ B ≅ A' ⊗ B`. -/
private noncomputable def rawTensorIsoLeft
    {X : AlgebraicGeometry.Scheme.{u}} {A A' B : X.Modules}
    (e : A ≅ A') :
    AlgebraicGeometry.Scheme.Modules.tensor A B ≅
      AlgebraicGeometry.Scheme.Modules.tensor A' B :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B ≪≫
    CategoryTheory.MonoidalCategory.tensorIso e (CategoryTheory.Iso.refl B) ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A' B).symm

/-- Auxiliary step for `foldZpowIso`: folding tensor products of powers of `L` onto `L ^ a ≅ A`. -/
private noncomputable def foldZpowIsoAux
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]
    (a : ℤ) (A : X.Modules) (e : L ^ a ≅ A) :
    (xs : List ℤ) →
      L ^ (a + xs.sum) ≅
        xs.foldl (fun G p => AlgebraicGeometry.Scheme.Modules.tensor G (L ^ p)) A
  | [] =>
      CategoryTheory.eqToIso (congrArg (fun z : ℤ => L ^ z) (by simp)) ≪≫ e
  | p :: xs => by
      let ep : L ^ (a + p) ≅
          AlgebraicGeometry.Scheme.Modules.tensor A (L ^ p) :=
        rawZpowAddIso L a p ≪≫ rawTensorIsoLeft (B := L ^ p) e
      let er := foldZpowIsoAux L (a + p)
        (AlgebraicGeometry.Scheme.Modules.tensor A (L ^ p)) ep xs
      exact CategoryTheory.eqToIso (congrArg (fun z : ℤ => L ^ z)
          (by simp [add_assoc])) ≪≫ er

/-- The fold `O ⊗ L^{x₁} ⊗ ⋯ ⊗ L^{xₙ}` is isomorphic to `L^{Σ xᵢ}`. -/
private noncomputable def foldZpowIso
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]
    (xs : List ℤ) :
    L ^ xs.sum ≅
      xs.foldl (fun G p => AlgebraicGeometry.Scheme.Modules.tensor G (L ^ p))
        (SheafOfModules.unit X.ringCatSheaf) :=
  CategoryTheory.eqToIso (congrArg (fun z : ℤ => L ^ z) (by simp)) ≪≫
    foldZpowIsoAux L 0 (SheafOfModules.unit X.ringCatSheaf)
    (CategoryTheory.eqToIso (show L ^ (0 : ℤ) =
      SheafOfModules.unit X.ringCatSheaf by rfl)) xs

private lemma totalDegree_aeval_sum_le {d : ℕ} (P : Polynomial ℚ) :
    (Polynomial.aeval (∑ i : Fin d, MvPolynomial.X i : MvPolynomial (Fin d) ℚ) P).totalDegree
      ≤ P.natDegree := by
  let S : MvPolynomial (Fin d) ℚ := ∑ i : Fin d, MvPolynomial.X i
  have hS : S.totalDegree ≤ 1 := by
    dsimp [S]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    simp
  rw [Polynomial.aeval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  rw [Finset.mem_range] at hi
  calc
    (P.coeff i • S ^ i).totalDegree ≤ (S ^ i).totalDegree :=
      MvPolynomial.totalDegree_smul_le _ _
    _ ≤ i * S.totalDegree := MvPolynomial.totalDegree_pow _ _
    _ ≤ i * 1 := Nat.mul_le_mul_left i hS
    _ = i := Nat.mul_one i
    _ ≤ P.natDegree := Nat.le_of_lt_succ hi

private lemma finRange_sum (d : ℕ) (n : Fin d → ℤ) :
    ((List.finRange d).map n).sum = ∑ i : Fin d, n i := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [List.finRange_succ, List.map_cons, List.sum_cons]
      rw [Fin.sum_univ_succ]
      congr 1
      simpa only [List.map_map, Function.comp_def] using ih (fun i => n i.succ)

/-- **The top self-intersection is `d!` times the leading coefficient of the Snapper polynomial**
`p ↦ χ(X, L^{⊗p})`, for `X` projective over `k` of dimension `d`. The projectivity hypothesis
`hXproj` comes from the comparison of the Snapper and Chow intersection numbers (Stacks 0BFI), which
is stated for projective schemes; in the deformation-invariance application `X` is a fiber of a
projective morphism. -/
theorem topSelfIntersection_eq_leadingCoeff {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (hXproj : IsProjectiveOver k X)
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (hd : X.dimension = d) (P : Polynomial ℚ)
    (hP : ∀ p : ℤ, (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (L ^ p) : ℚ)
      = P.eval (p : ℚ)) :
    (Nat.factorial d : ℚ) * P.coeff d
      = (AlgebraicGeometry.topSelfIntersection X hX L : ℚ) := by
  obtain ⟨P₀, hP₀deg, hP₀⟩ := exists_snapper_polynomial X hX L
  have hPeq : P = P₀ := by
    apply Polynomial.eq_of_infinite_eval_eq P P₀
    refine Set.Infinite.mono ?_
      (Set.Infinite.image
        (Set.injOn_of_injective
          (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ))))
        Set.infinite_univ)
    rintro x ⟨p, -, rfl⟩
    exact (hP p).symm.trans (hP₀ p)
  have hPdeg : P.natDegree ≤ d := by
    simpa [hPeq, hd] using hP₀deg
  let Q : MvPolynomial (Fin d) ℚ :=
    Polynomial.aeval
      (∑ i : Fin d, MvPolynomial.X i : MvPolynomial (Fin d) ℚ) P
  have hQχ : ∀ n : Fin d → ℤ,
      (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          ((List.finRange d).foldl
            (fun (G : X.Modules) (i : Fin d) => G.tensor (L ^ n i))
            (SheafOfModules.unit X.ringCatSheaf)) : ℚ)
        = MvPolynomial.eval (fun i => (n i : ℚ)) Q := by
    intro n
    let xs : List ℤ := (List.finRange d).map n
    have hsum : xs.sum = ∑ i : Fin d, n i := by
      exact finRange_sum d n
    have e : L ^ (∑ i : Fin d, n i) ≅
        (List.finRange d).foldl
          (fun (G : X.Modules) (i : Fin d) => G.tensor (L ^ n i))
          (SheafOfModules.unit X.ringCatSheaf) := by
      let e0 := foldZpowIso L xs
      rw [← hsum]
      have hmap :
          List.foldl (fun (G : X.Modules) (p : ℤ) => G.tensor (L ^ p))
              (SheafOfModules.unit X.ringCatSheaf) ((List.finRange d).map n) =
            List.foldl (fun (G : X.Modules) (i : Fin d) => G.tensor (L ^ n i))
              (SheafOfModules.unit X.ringCatSheaf) (List.finRange d) := by
        exact List.foldl_map (f := n)
          (g := fun (G : X.Modules) (p : ℤ) => G.tensor (L ^ p))
      exact e0.trans (CategoryTheory.eqToIso hmap)
    calc
      (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          ((List.finRange d).foldl
            (fun (G : X.Modules) (i : Fin d) => G.tensor (L ^ n i))
            (SheafOfModules.unit X.ringCatSheaf)) : ℚ)
          = (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
              (L ^ (∑ i : Fin d, n i)) : ℚ) := by
            rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso e]
      _ = P.eval ((∑ i : Fin d, n i : ℤ) : ℚ) := hP _
      _ = MvPolynomial.eval (fun i => (n i : ℚ)) Q := by
        dsimp [Q]
        norm_num [Int.cast_sum]
        change P.eval (∑ i : Fin d, (n i : ℚ)) =
          (MvPolynomial.aeval (fun i : Fin d => (n i : ℚ)))
            (Polynomial.aeval
              (∑ i : Fin d, MvPolynomial.X i : MvPolynomial (Fin d) ℚ) P)
        rw [← Polynomial.aeval_algHom_apply
          (MvPolynomial.aeval (fun i : Fin d => (n i : ℚ)))
          (∑ i : Fin d, MvPolynomial.X i : MvPolynomial (Fin d) ℚ) P]
        congr 1
        simp
  have hQdeg : Q.totalDegree ≤ d := by
    dsimp [Q]
    exact totalDegree_aeval_sum_le P |>.trans hPdeg
  have hcoeff := AlgebraicGeometry.snapperIntersection_eq_coeff X hX hd
    (fun _ : Fin d => L)
    (Polynomial.aeval
      (∑ i : Fin d, MvPolynomial.X i : MvPolynomial (Fin d) ℚ) P) hQdeg
      (by intro n; simpa [Q] using hQχ n)
  have htop := AlgebraicGeometry.snapperIntersection_self_eq_topSelfIntersection
    X hX hXproj hd L
  rw [← htop, hcoeff]
  exact (Polynomial.coeff_prod_X_comp_sum_X P hPdeg).symm

end
