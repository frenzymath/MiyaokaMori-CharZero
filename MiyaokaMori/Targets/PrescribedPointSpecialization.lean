import MiyaokaMori.Prelude
import MiyaokaMori.Targets.Realization
import MiyaokaMori.Paper.S4Completion.NefPullbackAmple
import MiyaokaMori.Paper.S4Completion.SpecialFiberRationalConnected
import MiyaokaMori.Paper.S4Completion.FiberDegreeIdentity
import MiyaokaMori.Paper.S4Completion.NonconstantComponentExists
import MiyaokaMori.Paper.S4Completion.PhiSigmaValue
import MiyaokaMori.Paper.S4Completion.ChainArgument
import MiyaokaMori.AlgebraicGeometry.Morphisms.NonconstantPrecomposeIso

/-! # Prescribed-point specialization

**Lemma 5.1** of the paper** (§5, "Prescribed-point specialization").

In the setting of Corollary 4.3 (the data `S, β, π_S, σ, Φ` returned by `realization`,
`Targets/Realization.lean`), put `A_S = Φ^*O_X(1)` and `d_F = A_S · F` for a smooth general fiber `F`
(in Lean: `fiberDegree πS hπS (Φ ^* O_X(1)) y₀` for a closed point `y₀` of the open set `V` of good
fibers). For every closed point `y ∈ C̃` there is a nonconstant `k`-morphism `b_y : P¹ → X` with
`b_y(0) = (f ∘ ρ)(y)` and `deg b_y^*O_X(1) ≤ d_F ≤ r₀`; `b_y` is `Φ` restricted to a noncontracted
component of `π_S^*(y)`, identified with `P¹`.

The main theorem (`miyaoka_mori`, `Targets/MainTheorem.lean`) is the case `x = (f∘ρ)(y)` of the
first three conclusions.

**Proof.**
1. `A_S` is nef (`nef_pullback_ample`: `O_X(1)` ample hence nef, pullbacks of nef are nef), and
   `1 ≤ d_F ≤ r₀` is the general-fiber statement of Corollary 4.3 (`hVfib` at `y₀`).
2. Fix a closed point `y`. The scheme-theoretic fiber is `π_S^*(y) = Σ m_i Γ_i` with `m_i ≥ 1`, each
   `Γ_i` a smooth rational curve, the union of the `Γ_i` the whole set-theoretic fiber, and the fiber
   connected (`special_fiber_rational_connected`: on the ruled surface the fiber is `P¹`, and each
   point blowup keeps the strict transforms smooth rational and the dual graph a tree).
3. All fibers of `π_S` are numerically equivalent (closed points of `C̃` are), so
   `Σ m_i (A_S·Γ_i) = A_S·F = d_F > 0` (`special_fiber_degree`; equation (5.1) of the paper).
4. Every summand is `≥ 0` (nef), so some `Γ_j` has `A_S·Γ_j > 0`, i.e. `Φ|_{Γ_j}` is nonconstant
   (`exists_nonconstant_component`; a constant restriction has degree `0`).
5. `σ(y)` lies in the fiber and `Φ(σ(y)) = f(ρ(y))` (`phi_sigma_eq` from `Φ∘σ = f∘ρ`). Walk along the
   connected fiber from a component containing `σ(y)` to a nonconstant component and stop at the first
   nonconstant one `Γ_{j'}`: the preceding components are constant with the same value at successive
   intersections, so `Γ_{j'}` contains a point `p` with `Φ(p) = f(ρ(y))` (`chain_to_nonconstant`).
6. `f(ρ(y))` is a closed point (`isClosed_singleton_image_of_isClosed_singleton`: k-morphisms of
   finite-type k-schemes send closed points to closed points), so `Φ|_{Γ_{j'}}^{-1}(f(ρ(y)))` is a
   nonempty closed subset of the Jacobson space `Γ_{j'}` and contains a closed point `q₀`.
7. `Γ_{j'} ≅ P¹` over `k` (`e₀`); `e₀(q₀)` is a closed point of `P¹`, hence has homogeneous coordinates
   `v ≠ 0` (`ProjectiveLine.exists_coords_of_isClosed`), and a linear automorphism `g` of `P¹` with
   `g(0) = e₀(q₀)` exists (`ProjectiveLine.exists_aut_of_matrix` with the matrix `[[0, v₀],[1, v₁]]` if
   `v₀ ≠ 0`, `[[1,0],[0,v₁]]` otherwise). Put `b := g ∘ e₀⁻¹ ∘ ι_{Γ_{j'}} ∘ Φ`: a k-morphism,
   nonconstant (precomposition with isomorphisms, `nonconstant_comp_iso`), with `b(0) = f(ρ(y))`.
8. Degree: with `e := e₀⁻¹ ∘ g : P¹ ≅ Γ_{j'}`, `b^*O_X(1) = (e ∘ ι)^* A_S` (`Modules.pullbackComp`), whose
   degree on `P¹` is `A_S · Γ_{j'}` (`IntegralCurve.degree_pullback_of_iso_projectiveLine` below: `P¹ → S` is a
   closed immersion with the same image, so it defines the same one-cycle `[Γ_{j'}]`
   (`fundamentalClass_coe_eq_single` at the image of the generic point), and
   `A ⬝ [Γ] = deg(ι^*A)` by `inter_fundamentalClass_eq_degree` + `degree_eq_lineBundle_degree_pullback`).
   Finally `A_S·Γ_{j'} ≤ m_{j'}(A_S·Γ_{j'}) ≤ Σ m_i (A_S·Γ_i) = d_F` (all terms `≥ 0`, `m_{j'} ≥ 1`),
   and `d_F ≤ r₀` is the embedding bound (4.5) of the paper.

Hypotheses are exactly (a subset of) the data returned by `realization`; the conjuncts of
`realization` not used here (`hDisj`, `hproj`, `hconn`, `hσβ`, `hEmb`, the jet data) are omitted, so the
statement is formally stronger than "in the setting of Corollary 4.3".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Degree along `P¹ ≅ Γ ↪ S`.** If `Γ ⊂ S` is an integral curve and `e : P¹ ≅ Γ` an isomorphism of
schemes, then the degree on `P¹` of `(e ≫ ι_Γ)^* A` equals the intersection number `A ⬝ [Γ]`.
Proof: `e ≫ ι_Γ` is a closed immersion `P¹ → S` with the same image, so it is an integral curve `Γ'`
whose fundamental class is the one-point cycle at the image of the generic point
(`IntegralCurve.fundamentalClass_coe_eq_single`), and isomorphisms map generic points to generic
points (`AlgebraicGeometry.Scheme.dominantMap_genericPoint`), so `[Γ'] = [Γ]`. Then `A ⬝ [Γ'] = Γ'.degree A`
(`LineBundle.inter_fundamentalClass_eq_degree`) `= deg((e ≫ ι_Γ)^* A)` on the smooth projective curve
`P¹` (`IntegralCurve.degree_eq_lineBundle_degree_pullback`). Used for the degree bound of
Lemma 5.1. -/
theorem IntegralCurve.degree_pullback_of_iso_projectiveLine {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} (A : LineBundle S.toVariety)
    (Γ : IntegralCurve k S.toScheme) (e : ProjectiveLine k ≅ Γ.carrier) :
    (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
      (e.hom ≫ Γ.ι) A).degree = A ⬝ Γ.fundamentalClass := by
  haveI : AlgebraicGeometry.IsIntegral (ProjectiveLine.asSmoothProjectiveCurve k).toScheme :=
    SmoothProjectiveCurve.isIntegral _
  haveI : AlgebraicGeometry.IsProper
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    SmoothProjectiveVariety.isProper_structureMorphism S.toSmoothProjectiveVariety
  haveI : AlgebraicGeometry.IsClosedImmersion (e.hom ≫ Γ.ι) := inferInstance
  let Γ' : IntegralCurve k S.toScheme :=
    { carrier := (ProjectiveLine.asSmoothProjectiveCurve k).toScheme
      ι := e.hom ≫ Γ.ι
      dim_eq_one := (ProjectiveLine.asSmoothProjectiveCurve k).dim_one }
  have hgen : e.hom.base (genericPoint (ProjectiveLine k)) = genericPoint Γ.carrier :=
    AlgebraicGeometry.Scheme.dominantMap_genericPoint e.hom
  have hfund : Γ'.fundamentalClass = Γ.fundamentalClass := by
    classical
    apply Subtype.ext
    rw [IntegralCurve.fundamentalClass_coe_eq_single, IntegralCurve.fundamentalClass_coe_eq_single]
    change Function.locallyFinsuppWithin.single
      (Γ.ι.base (e.hom.base (genericPoint (ProjectiveLine k)))) (1 : ℤ) = _
    rw [hgen]
  rw [← hfund, LineBundle.inter_fundamentalClass_eq_degree]
  exact (IntegralCurve.degree_eq_lineBundle_degree_pullback (X := S.toVariety)
    (C := ProjectiveLine.asSmoothProjectiveCurve k) (e.hom ≫ Γ.ι) A).symm

/-- **Prescribed-point specialization** (Lemma 5.1 of the paper): for every closed
point `y` of `C̃` there is a nonconstant `k`-morphism `b : P¹ → X` with `b(0) = f(ρ(y))` and
`deg b^*O_X(1) ≤ d_F ≤ r₀`. See the module docstring for the proof. -/
theorem prescribed_point_specialization {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (r₀ : ℕ)
    (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ (ruledSurface L).toScheme)
    (hβ : IsBlowupTower β)
    (eW : (ruledSurface L).toScheme ≅
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := ρ.source.toVariety.toScheme.Modules)
          (show ρ.source.toVariety.toScheme.Modules from
            SheafOfModules.unit ρ.source.toVariety.toScheme.ringCatSheaf) L.toModules)).left)
    (πS : S.toScheme ⟶ ρ.source.toScheme) (hπS : AlgebraicGeometry.Surjective πS)
    (σ : ρ.source.toScheme ⟶ S.toScheme) (Φ : S.toScheme ⟶ X.toScheme)
    (hAvoid : IsBlowupTowerAvoiding β
      (Set.range (AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv).base))
    (hπfac : πS = β ≫ ruledSurface.π L)
    (hσπ : σ ≫ πS = CategoryTheory.CategoryStruct.id ρ.source.toScheme)
    (hσΦ : σ ≫ Φ = ρ.hom ≫ f)
    (hΦover : Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (V : Set ρ.source.toScheme)
    (hVfib : ∀ y ∈ V, IsClosed ({y} : Set ρ.source.toScheme) →
      Nonempty ((πS.fiber y) ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme) ∧
      1 ≤ fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y ∧
      fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y ≤ (r₀ : ℤ))
    (y₀ : ρ.source.toScheme) (hy₀V : y₀ ∈ V) (hy₀ : IsClosed ({y₀} : Set ρ.source.toScheme))
    (y : ρ.source.toScheme) (hy : IsClosed ({y} : Set ρ.source.toScheme)) :
    ∃ b : ProjectiveLine k ⟶ X.toScheme,
      b.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      ¬ IsConstantMorphism b ∧
      b.base (ProjectiveLine.zero k) = (ρ.hom ≫ f).base y ∧
      (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
        b (X.OX 1)).degree ≤
        fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y₀ ∧
      fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y₀ ≤ (r₀ : ℤ) := by
  -- The prescribed value x = f(ρ(y)); it is a closed point.
  set x : X.toScheme := (ρ.hom ≫ f).base y with hxdef
  have hfy : f.base (ρ.hom.base y) = x := rfl
  have hxc : IsClosed ({x} : Set X.toScheme) := by
    have hg : (ρ.hom ≫ f) ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := by
      rw [Category.assoc, CategoryTheory.comp_over f (AlgebraicGeometry.Spec (CommRingCat.of k))]
      exact ρ.isOver
    exact AlgebraicGeometry.isClosed_singleton_image_of_isClosed_singleton
      (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (ρ.hom ≫ f) hg y hy
  -- k-structures of β and π_S.
  have hβover : β.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsBlowupTower.isOver hβ
  letI : β.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := hβover
  have hπW : (ruledSurface.π L).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [AlgebraicGeometry.Scheme.Hom.isOver_iff]
    rfl
  letI : πS.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    refine ⟨?_⟩
    rw [hπfac, Category.assoc, hπW.1, hβover.1]
  -- A_S = Φ^*O_X(1), d_F = A_S · F.
  let A : LineBundle S.toVariety :=
    LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)
  obtain ⟨-, hdf₁, hdfupper⟩ := hVfib y₀ hy₀V hy₀
  let dF : ℤ := fiberDegree πS hπS A y₀
  have hdF : 0 < dF := by
    dsimp [dF, A]
    omega
  have hnef : IsNef A := by
    simpa [A] using (nef_pullback_ample Φ).1
  -- The fiber over y: a connected union of smooth rational components Γ_i with multiplicities m_i.
  obtain ⟨ι, hι, m, Γ, hm, hdec, hcov, hconnfiber, hΓrat⟩ :=
    special_fiber_rational_connected L β hβ hAvoid πS hπfac hπS y hy
  letI : Fintype ι := hι
  have hsum : ∑ i, (m i : ℤ) * (A ⬝ (Γ i).fundamentalClass) = dF :=
    special_fiber_degree πS hπS A y y₀ hy hy₀ hdec
  obtain ⟨j, hjpos, hjnc⟩ := exists_nonconstant_component Φ hm hnef hdF hsum
  have hxσ : Φ.base (σ.base y) = x := phi_sigma_eq Φ σ ρ.hom f hσΦ y x hfy
  obtain ⟨j', hj'nc, p, hp, hpx⟩ :=
    chain_to_nonconstant Φ πS hπS σ hσπ y x hxσ hcov hconnfiber ⟨j, hjnc⟩
  obtain ⟨q, hq⟩ := hp
  have hqX : ((Γ j').ι ≫ Φ).base q = x := by
    change Φ.base ((Γ j').ι.base q) = x
    rw [hq]
    exact hpx
  -- A closed point q₀ of Γ_{j'} over x.
  letI : AlgebraicGeometry.LocallyOfFiniteType
      ((Γ j').carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (Γ j').isProper.toLocallyOfFiniteType
  letI : JacobsonSpace (Γ j').carrier :=
    AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
      ((Γ j').carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let ZΓ : Set (Γ j').carrier := ((Γ j').ι ≫ Φ).base ⁻¹' {x}
  have hcont : Continuous ((Γ j').ι ≫ Φ).base := by
    change Continuous (Φ.base ∘ (Γ j').ι.base)
    exact Φ.continuous.comp (Γ j').ι.continuous
  have hZΓ : IsClosed ZΓ := hxc.preimage hcont
  have hZΓne : ZΓ.Nonempty := ⟨q, hqX⟩
  obtain ⟨q₀, hq₀Z, hq₀⟩ := nonempty_inter_closedPoints
    (Z := ZΓ) hZΓne hZΓ.isLocallyClosed
  have hq₀X : ((Γ j').ι ≫ Φ).base q₀ = x := hq₀Z
  -- Γ_{j'} ≅ P¹ and a linear automorphism g of P¹ with g(0) = e₀(q₀).
  obtain ⟨e₀, he₀⟩ := hΓrat j'
  let p₀ : ProjectiveLine k := e₀.hom.base q₀
  have hp₀closed : IsClosed ({p₀} : Set (ProjectiveLine k)) := by
    have hh := e₀.hom.homeomorph.isClosedMap ({q₀} : Set (Γ j').carrier) hq₀
    simpa [p₀, AlgebraicGeometry.Scheme.Hom.homeomorph_apply] using hh
  obtain ⟨v, hv, hp₀v⟩ := ProjectiveLine.exists_coords_of_isClosed p₀ hp₀closed
  have hexg :
      ∃ (g : ProjectiveLine k ≅ ProjectiveLine k),
        g.hom ≫ ProjectiveSpace.toSpecBase 1 k = ProjectiveSpace.toSpecBase 1 k ∧
          g.hom.base (ProjectiveLine.zero k) = p₀ := by
    by_cases hv0 : v 0 ≠ 0
    · let M : Matrix (Fin 2) (Fin 2) k := !![0, v 0; 1, v 1]
      have hdet : IsUnit M.det := by
        rw [show M = !![0, v 0; 1, v 1] by rfl, Matrix.det_fin_two_of]
        apply isUnit_iff_ne_zero.mpr
        simp [hv0]
      obtain ⟨g, hgbase, hgcoord⟩ := ProjectiveLine.exists_aut_of_matrix M hdet
      have hg0 : g.hom.base (ProjectiveLine.zero k) = p₀ := by
        obtain ⟨hMv, hh⟩ := hgcoord ![0, 1] (by simp)
        rw [ProjectiveLine.ofCoords_zero] at hh
        have hMv_eq : M.mulVec ![0, 1] = v := by
          ext i
          fin_cases i <;> simp [M]
        rw [hp₀v]
        simpa [hMv_eq] using hh
      exact ⟨g, hgbase, hg0⟩
    · have hv0' : v 0 = 0 := by exact not_ne_iff.mp hv0
      have hv1 : v 1 ≠ 0 := by
        intro h
        apply hv
        funext i
        fin_cases i <;> simp [hv0', h]
      let M : Matrix (Fin 2) (Fin 2) k := !![1, 0; 0, v 1]
      have hdet : IsUnit M.det := by
        rw [show M = !![1, 0; 0, v 1] by rfl, Matrix.det_fin_two_of]
        apply isUnit_iff_ne_zero.mpr
        simpa using hv1
      obtain ⟨g, hgbase, hgcoord⟩ := ProjectiveLine.exists_aut_of_matrix M hdet
      have hg0 : g.hom.base (ProjectiveLine.zero k) = p₀ := by
        obtain ⟨hMv, hh⟩ := hgcoord ![0, 1] (by simp)
        rw [ProjectiveLine.ofCoords_zero] at hh
        have hMv_eq : M.mulVec ![0, 1] = v := by
          ext i
          fin_cases i <;> simp [M, hv0']
        rw [hp₀v]
        simpa [hMv_eq] using hh
      exact ⟨g, hgbase, hg0⟩
  obtain ⟨g, hgbase, hg0⟩ := hexg
  have he₀inv : e₀.inv.IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    refine ⟨?_⟩
    rw [← he₀, ← Category.assoc, e₀.inv_hom_id, Category.id_comp]
  have hΓover : (Γ j').ι.IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    exact ⟨rfl⟩
  have hgbase' : g.hom ≫ (ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := by
    exact hgbase
  -- b := Φ ∘ ι_{Γ_{j'}} ∘ e, with e = e₀⁻¹ ∘ g : P¹ ≅ Γ_{j'}.
  let e : ProjectiveLine k ≅ (Γ j').carrier := g ≪≫ e₀.symm
  let ι' : ProjectiveLine k ⟶ S.toScheme := e.hom ≫ (Γ j').ι
  let b : ProjectiveLine k ⟶ X.toScheme := ι' ≫ Φ
  have hb : b = g.hom ≫ e₀.inv ≫ (Γ j').ι ≫ Φ := by
    simp only [b, ι', e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hbOver : b.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [AlgebraicGeometry.Scheme.Hom.isOver_iff, hb]
    simp only [Category.assoc]
    rw [hΦover.1, hΓover.1, he₀inv.1, hgbase']
  have hnc : ¬ IsConstantMorphism b := by
    rw [hb]
    exact nonconstant_comp_iso g (nonconstant_comp_iso e₀.symm hj'nc)
  have he₀inv_point : e₀.inv.base p₀ = q₀ := by
    have hh := congrArg (fun t => t.base q₀) e₀.hom_inv_id
    change e₀.inv.base (e₀.hom.base q₀) = q₀ at hh
    exact hh
  have hb0 : b.base (ProjectiveLine.zero k) = x := by
    rw [hb]
    change Φ.base ((Γ j').ι.base
      (e₀.inv.base (g.hom.base (ProjectiveLine.zero k)))) = x
    rw [hg0, he₀inv_point]
    exact hq₀X
  -- Degree bound: deg b^*O_X(1) = A_S · Γ_{j'} ≤ Σ m_i (A_S · Γ_i) = d_F.
  have hbdeg : (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
      b (X.OX 1)).degree = A ⬝ (Γ j').fundamentalClass := by
    rw [← IntegralCurve.degree_pullback_of_iso_projectiveLine A (Γ j') e]
    exact (LineBundle.degree_congr
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp ι' Φ).app (X.OX 1).toModules)).symm
  have hterm : A ⬝ (Γ j').fundamentalClass ≤ dF := by
    rw [← hsum]
    have hm1 : (1 : ℤ) ≤ (m j' : ℤ) := by exact_mod_cast hm j'
    have h1 : A ⬝ (Γ j').fundamentalClass ≤ (m j' : ℤ) * (A ⬝ (Γ j').fundamentalClass) :=
      le_mul_of_one_le_left (hnef (Γ j')) hm1
    refine h1.trans (Finset.single_le_sum
      (f := fun i => (m i : ℤ) * (A ⬝ (Γ i).fundamentalClass)) ?_ (Finset.mem_univ j'))
    intro i _
    exact mul_nonneg (by exact_mod_cast Nat.zero_le (m i)) (hnef (Γ i))
  refine ⟨b, hbOver, hnc, hb0, ?_, hdfupper⟩
  rw [hbdeg]
  exact hterm

end
