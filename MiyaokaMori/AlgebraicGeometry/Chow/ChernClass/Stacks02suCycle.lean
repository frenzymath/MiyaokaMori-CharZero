import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapLocallyFiniteSum
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02st

/-! # The projection formula at the level of cycles (Stacks 02SU)

Stacks 02SU (projection formula at the level of cycles): `X`, `Y` locally of finite type over a field,
`p : X → Y` proper, `L` an invertible sheaf on `Y`, `α` a `(d+1)`-cycle on `X`; then
`p_*(c_1(p^*L) ∩ α) = c_1(L) ∩ p_*α` in `CH_d(Y)`. Here `∩` is the cycle-level operation (Stacks 02SO,
`firstChernCapCycle`, with values in the Chow group), not the descent of `c_1` to the Chow group, so
the proof of the descent (Stacks 02TI) may use this result without circularity.

Source: Stacks 02SU. The Stacks proof writes `α = Σ n_i [W_i]`, lets `W′_i ⊆ Y` be the image of `W_i`
(an integral closed subscheme), and factors `p` as `X′ = ∐ W_i → Y′ = ∐ W′_i` between closed immersions
`q`, `q′`; the closed-immersion half is a special case, which reduces to "`X`, `Y` integral, `p`
dominant, `α = [X]`", i.e. Stacks 02ST (`Stacks02st.lean`), whose missing piece, the pullback of
rational sections along dominant morphisms, is `RationalSectionPullbackDominant.lean`.

The route actually formalized (Stacks 02SU, proof,
reorganised so that every rationally trivial piece is either a single generator at `p w` or comes from Stacks 02S2):
1. Reduction to points. Both sides of the identity are locally finite sums over
   `S = {w | height w = d + 1 ∧ α w ≠ 0}` (`firstChernCapCycleAux_apply_eq_finsum_subtype`,
   `apply_eq_finsum_single_subtype`, `properPushforward_of_locallyFiniteSum`,
   `firstChernCapCycleAux_of_locallyFiniteSum`), and `ratEquivZero_of_locallyFinite_sum` is applied with
   `T w = closure {p w}` — a locally finite family because `p` is quasi-compact
   (`locallyFinitePoints_comp_of_quasiCompact`).
2. One point `w` (`firstChernCapPoint_properPushforward_sub_mem`). Factor `ι_w ≫ p = q ≫ ι_{p w}` through
   `Y.pointClosure (p w)` (`exists_hom_pointClosure`: scheme-theoretic image + `exists_iso_pointClosure_of_isClosedImmersion`);
   `q` is proper (`IsProper.of_comp`) and dominant. Write `c_1(p^*L) ∩ [w] = ι_{w*} div(s)`, transport `s` to `q^*N`
   with `N = ι_{p w}^*L`, and compare with the pullback `q^*s'` of a rational section `s'` of `N` (02SH):
   `div(s) = div(q^*s') + div(g)`. The principal part `ι_{p w *} q_* div(g)` is rationally trivial by **Stacks 02S2
   (statement only: `properPushforward_rationallyEquivalent`)**, pushed along the closed immersion
   (`properPushforward_pointClosure_mem_ratEquivZeroOn`).
   - `height (p w) = d + 1`: `q_* div(q^*s') = deg · div_N(s')` (02ST at the divisor level,
     `properPushforward_rationalSectionDivisor_pullback`), `p_*[w] = deg · [p w]` (`properPushforward_single`), and
     `c_1(L) ∩ [p w] = ι_{p w *} div_N(s') + (generators at p w)` (02SH + the closed-immersion case
     `exists_firstChernCapPoint_sub_eq_principalCycle`).
   - `height (p w) < d + 1`: `p_*[w] = 0` and `q_* div(q^*s') = 0`
     (`properPushforward_rationalSectionDivisor_pullback_eq_zero_of_lt`: by Stacks 0A21 a nonzero
     coefficient would sit over `η_{W'}`, where `q^*s'` has order `0` because it is the image of a unit of `O_{W',η}`).
   In particular the norm formula 02RT is not used; the geometric input entering through this
   file is Stacks 02S2 (`properPushforward_scheme_core`).
Two pitfalls: `L.stalk x` and `L.presheaf.stalk x` are not reducibly defeq, so `rw`
fails on goals mixing them — name the pulled-back section with `set t : (…).stalk _ := rationalSectionPullback …`; and the
root abbreviation `AlgebraicGeometry.AlgebraicCycle.properPushforward` is a different head symbol from
`AlgebraicGeometry.AlgebraicCycle.properPushforward`, so library lemmas are restated in root form (`pp_comp`, …).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.Stacks02suCycle

open AlgebraicGeometry MiyaokaMori.ClosedImmersionPushforward MiyaokaMori.FirstChernCapPointGeneric
  MiyaokaMori.FirstChernCapPointClosurePushforward MiyaokaMori.PointClosureTransport

/-! ### 1. General bookkeeping for proper pushforward of cycles -/

/-! Root-namespace restatements of the pushforward algebra (the library states them for
`AlgebraicGeometry.AlgebraicCycle.properPushforward`; this file, like the target statement, uses the
root abbreviation `AlgebraicGeometry.AlgebraicCycle.properPushforward`, and `rw` matches syntactically). -/

theorem pp_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g]
    (c : AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward g (AlgebraicGeometry.AlgebraicCycle.properPushforward f c) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward (f ≫ g) c :=
  AlgebraicGeometry.AlgebraicCycle.properPushforward_comp f g c

theorem pp_add {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (a b : AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f (a + b) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward f a + AlgebraicGeometry.AlgebraicCycle.properPushforward f b :=
  AlgebraicGeometry.properPushforward_add f a b

theorem pp_zsmul {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (n : ℤ) (a : AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f (n • a) = n • AlgebraicGeometry.AlgebraicCycle.properPushforward f a :=
  AlgebraicGeometry.AlgebraicCycle.properPushforward_zsmul f n a

theorem pp_zero {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f (0 : AlgebraicCycle X ℤ) = 0 :=
  (AlgebraicGeometry.AlgebraicCycle.properPushforwardHom f).map_zero

/-- The coefficient formula of `properPushforward` (Mathlib `AlgebraicCycle.map`), by definition. -/
theorem properPushforward_apply' {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (c : AlgebraicCycle X ℤ) (z : Y) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f c z =
      ∑ᶠ x ∈ f.base ⁻¹' {z}, c x *
        ((AlgebraicCycle.mapCoeff f (Order.height (α := X)) (Order.height (α := Y)) x : ℕ) : ℤ) :=
  rfl

/-- A nonzero coefficient of `f_*c` at `z` comes from a point of the fibre with nonzero coefficient. -/
theorem exists_of_properPushforward_apply_ne_zero {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (c : AlgebraicCycle X ℤ) {z : Y} (h : AlgebraicGeometry.AlgebraicCycle.properPushforward f c z ≠ 0) :
    ∃ x, f.base x = z ∧ c x ≠ 0 := by
  rw [properPushforward_apply'] at h
  obtain ⟨x, hx, hne⟩ := exists_ne_zero_of_finsum_mem_ne_zero h
  exact ⟨x, hx, left_ne_zero_of_mul hne⟩

/-- Pushforward of a one-point cycle: `f_*(n·[x]) = (n · mapCoeff f x)·[f x]`. -/
theorem properPushforward_single {X Y : Scheme.{u}} [DecidableEq X] [DecidableEq Y]
    (f : X ⟶ Y) [IsProper f] (x : X) (n : ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f (Function.locallyFinsuppWithin.single x n) =
      Function.locallyFinsuppWithin.single (f.base x)
        (n * ((AlgebraicCycle.mapCoeff f (Order.height (α := X)) (Order.height (α := Y)) x : ℕ) : ℤ)) := by
  classical
  ext z
  rw [properPushforward_apply', Function.locallyFinsuppWithin.single_apply, finsum_mem_def]
  have hsupp : ∀ x', x' ≠ x → (f.base ⁻¹' {z}).indicator
      (fun x' => Function.locallyFinsuppWithin.single x n x' *
        ((AlgebraicCycle.mapCoeff f (Order.height (α := X)) (Order.height (α := Y)) x' : ℕ) : ℤ)) x'
        = 0 := by
    intro x' hx'
    rw [Set.indicator_apply]
    split_ifs
    · rw [Function.locallyFinsuppWithin.single_apply, if_neg hx', zero_mul]
    · rfl
  rw [finsum_eq_single _ x hsupp, Set.indicator_apply, Function.locallyFinsuppWithin.single_apply, if_pos rfl]
  by_cases hz : z = f.base x
  · rw [if_pos hz, if_pos (by simp [hz])]
  · rw [if_neg hz, if_neg (by simpa [eq_comm] using hz)]

/-- Pushforward of a one-point cycle along a closed immersion: `i_*(n·[x]) = n·[i x]`. -/
theorem properPushforward_single_of_isClosedImmersion {X Y : Scheme.{u}} [DecidableEq X]
    [DecidableEq Y] (i : X ⟶ Y) [IsClosedImmersion i] (x : X) (n : ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward i (Function.locallyFinsuppWithin.single x n) =
      Function.locallyFinsuppWithin.single (i.base x) n := by
  ext z
  by_cases hz : z ∈ Set.range i.base
  · obtain ⟨z', rfl⟩ := hz
    rw [properPushforward_closedImmersion_apply, Function.locallyFinsuppWithin.single_apply,
      Function.locallyFinsuppWithin.single_apply]
    have hinj : Function.Injective i.base := i.isClosedEmbedding.injective
    by_cases h : z' = x
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (hinj h'))]
  · rw [properPushforward_apply_of_notMem_range i _ hz, Function.locallyFinsuppWithin.single_apply,
      if_neg (fun h => hz ⟨x, h.symm⟩)]

/-- The image of a locally finite family of points under a quasi-compact morphism is locally
finite (a compact preimage meets only finitely many of the closures `closure {w j}`). -/
theorem locallyFinitePoints_comp_of_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {J : Type v} {w : J → X} (hw : LocallyFinitePoints w) :
    LocallyFinitePoints (fun j => f.base (w j)) := by
  intro y
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  refine ⟨V, V.isOpen, hyV, ?_⟩
  have hcpt : IsCompact (f.base ⁻¹' (V : Set Y)) :=
    QuasiCompact.isCompact_preimage (f := f) V V.isOpen hV.isCompact
  have hlf := (locallyFinitePoints_iff_locallyFinite_closure w).mp hw
  refine (hlf.finite_nonempty_inter_compact hcpt).subset ?_
  intro j hj
  exact ⟨w j, subset_closure rfl, hj⟩

/-- `properPushforward` commutes with locally finite sums of cycles: if `γ = Σ_j c j` pointwise,
each `c j` is supported in `closure {w j}` and `{w j}` is locally finite, then
`f_*γ = Σ_j f_*(c j)` pointwise. -/
theorem properPushforward_of_locallyFiniteSum {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {J : Type v} {w : J → X} {c : J → AlgebraicCycle X ℤ} (hlf : LocallyFinitePoints w)
    (hsup : ∀ (j : J) (t : X), c j t ≠ 0 → w j ⤳ t)
    (γ : AlgebraicCycle X ℤ) (hγ : ∀ t, γ t = ∑ᶠ j, c j t) (z : Y) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f γ z =
      ∑ᶠ j, AlgebraicGeometry.AlgebraicCycle.properPushforward f (c j) z := by
  classical
  set m : X → ℤ := fun x =>
    ((AlgebraicCycle.mapCoeff f (Order.height (α := X)) (Order.height (α := Y)) x : ℕ) : ℤ) with hm
  let F : X × J → ℤ := fun q => (f.base ⁻¹' {z}).indicator (fun x => c q.2 x * m x) q.1
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hzV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hcpt : IsCompact (f.base ⁻¹' (V : Set Y)) :=
    QuasiCompact.isCompact_preimage (f := f) V V.isOpen hVaff.isCompact
  obtain ⟨U₁, hU₁, hzU₁, hJfin⟩ := locallyFinitePoints_comp_of_quasiCompact f hlf z
  have hFsupp : Function.support F ⊆
      ⋃ j ∈ {j : J | f.base (w j) ∈ U₁},
        ((f.base ⁻¹' (V : Set Y)) ∩ Function.support (c j : X → ℤ)) ×ˢ ({j} : Set J) := by
    rintro ⟨x, j⟩ hxj
    have hxj' : F (x, j) ≠ 0 := hxj
    simp only [F, Set.indicator_apply] at hxj'
    split_ifs at hxj' with hx
    · have hxz : f.base x = z := hx
      have hcj : c j x ≠ 0 := left_ne_zero_of_mul hxj'
      have hwj : f.base (w j) ∈ U₁ :=
        (((hsup j x hcj).map f.continuous).trans (specializes_of_eq hxz)).mem_open hU₁ hzU₁
      exact Set.mem_biUnion hwj ⟨⟨by rw [Set.mem_preimage, hxz]; exact hzV, hcj⟩, rfl⟩
    · exact absurd rfl hxj'
  have hFfin : Function.HasFiniteSupport F :=
    (hJfin.biUnion (fun j _ =>
      (((c j).locallyFiniteSupport.finite_inter_support_of_isCompact hcpt).prod
        (Set.finite_singleton j)))).subset hFsupp
  have hGfin : Function.HasFiniteSupport (fun q : J × X => F (Equiv.prodComm J X q)) :=
    hFfin.preimage (Equiv.injective (Equiv.prodComm J X)).injOn
  have hstep : ∀ x : X, (f.base ⁻¹' {z}).indicator (fun x => γ x * m x) x = ∑ᶠ j, F (x, j) := by
    intro x
    simp only [F, Set.indicator_apply]
    split_ifs
    · rw [hγ x, finsum_mul]
    · rw [finsum_zero]
  rw [properPushforward_apply', finsum_mem_def, finsum_congr hstep,
    ← finsum_curry F hFfin, ← finsum_comp_equiv (Equiv.prodComm J X) (f := F),
    finsum_curry _ hGfin]
  refine finsum_congr fun j => ?_
  rw [properPushforward_apply', finsum_mem_def]
  rfl

/-! ### 2. Bookkeeping for `firstChernCapCycleAux` -/

theorem firstChernCapCycleAux_zsmul {X : Scheme.{u}} [IsLocallyNoetherian X] (L : X.Modules)
    [L.IsLineBundle] (d : ℕ) (n : ℤ) (α : AlgebraicCycle X ℤ) :
    firstChernCapCycleAux L d (n • α) = n • firstChernCapCycleAux L d α :=
  map_zsmul (AddMonoidHom.mk' (firstChernCapCycleAux L d) (firstChernCapCycleAux_add L d)) n α

/-- `c_1(L) ∩ (n·[y]) = n · (c_1(L) ∩ [y])` when `y` has the right dimension, `0` otherwise. -/
theorem firstChernCapCycleAux_single {X : Scheme.{u}} [IsLocallyNoetherian X] [DecidableEq X]
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (y : X) (n : ℤ) :
    firstChernCapCycleAux L d (Function.locallyFinsuppWithin.single y n) =
      if Order.height y = (d : ℕ∞) then n • firstChernCapPoint L y else 0 := by
  ext z
  show (∑ᶠ w : X, firstChernCapTerm L d (Function.locallyFinsuppWithin.single y n) z w) = _
  have hsupp : ∀ w, w ≠ y → firstChernCapTerm L d (Function.locallyFinsuppWithin.single y n) z w = 0 := by
    intro w hw
    unfold firstChernCapTerm
    split_ifs
    · rw [Function.locallyFinsuppWithin.single_apply, if_neg hw, zero_mul]
    · rfl
  rw [finsum_eq_single _ y hsupp]
  unfold firstChernCapTerm
  split_ifs with h
  · rw [Function.locallyFinsuppWithin.single_apply, if_pos rfl, AlgebraicCycle.zsmul_apply]
  · rfl

/-- A nonzero coefficient of `c_1(L) ∩ β` at `z` comes from a point of `supp β` specializing to `z`. -/
theorem exists_of_firstChernCapCycleAux_apply_ne_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (β : AlgebraicCycle X ℤ) {z : X}
    (h : firstChernCapCycleAux L d β z ≠ 0) : ∃ w, β w ≠ 0 ∧ w ⤳ z := by
  have : ∃ w, firstChernCapTerm L d β z w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h (by show (∑ᶠ w : X, _) = 0; simp [hall])
  obtain ⟨w, hw⟩ := this
  obtain ⟨-, hβ, hc⟩ := firstChernCapTerm_ne_zero L hw
  exact ⟨w, hβ, firstChernCapPoint_specializes L hc⟩

/-- The linear extension written as a sum over the support of the right dimension. -/
theorem firstChernCapCycleAux_apply_eq_finsum_subtype {X : Scheme.{u}} [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (α : AlgebraicCycle X ℤ) (z : X) :
    firstChernCapCycleAux L d α z =
      ∑ᶠ j : {w : X | Order.height w = (d : ℕ∞) ∧ α w ≠ 0},
        α (j : X) * firstChernCapPoint L (j : X) z := by
  show (∑ᶠ w : X, firstChernCapTerm L d α z w) = _
  set S : Set X := {w : X | Order.height w = (d : ℕ∞) ∧ α w ≠ 0} with hS
  have hsupp : Function.support (firstChernCapTerm L d α z) ⊆ S := fun w hw =>
    ⟨(firstChernCapTerm_ne_zero L hw).1, (firstChernCapTerm_ne_zero L hw).2.1⟩
  have hinter : Set.univ ∩ Function.support (firstChernCapTerm L d α z) =
      S ∩ Function.support (firstChernCapTerm L d α z) := by
    rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp]
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq _ Set.univ S hinter,
    ← finsum_set_coe_eq_finsum_mem S]
  refine finsum_congr fun j => ?_
  unfold firstChernCapTerm
  rw [if_pos j.2.1]

/-- A `d`-cycle is the locally finite sum of its one-point pieces (pointwise). -/
theorem apply_eq_finsum_single_subtype {X : Scheme.{u}} [DecidableEq X] (d : ℕ)
    (α : AlgebraicCycle X ℤ) (hα : α ∈ cycleSubgroup X d) (t : X) :
    α t = ∑ᶠ j : {w : X | Order.height w = (d : ℕ∞) ∧ α w ≠ 0},
      (α (j : X) • Function.locallyFinsuppWithin.single (j : X) (1 : ℤ)) t := by
  by_cases ht : α t = 0
  · rw [ht]
    symm
    refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
    rw [AlgebraicCycle.zsmul_apply, Function.locallyFinsuppWithin.single_apply]
    split_ifs with h
    · exact absurd (h ▸ ht) j.2.2
    · rw [mul_zero]
  · have hS : t ∈ {w : X | Order.height w = (d : ℕ∞) ∧ α w ≠ 0} := ⟨hα t ht, ht⟩
    rw [finsum_eq_single _ ⟨t, hS⟩ (fun j hj => by
      rw [AlgebraicCycle.zsmul_apply, Function.locallyFinsuppWithin.single_apply,
        if_neg (fun h => hj (Subtype.ext h.symm)), mul_zero])]
    rw [AlgebraicCycle.zsmul_apply, Function.locallyFinsuppWithin.single_apply, if_pos rfl, mul_one]


/-! ### 3. The geometric core: one point at a time -/

attribute [local instance] AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure

/-- Factor `ι_w ≫ p : closure{w} → Y` through the reduced closed subscheme `Y.pointClosure (p w)`
(via the scheme-theoretic image of `ι_w ≫ p`, which is `≅ Y.pointClosure (p w)` by
`exists_iso_pointClosure_of_isClosedImmersion`). -/
theorem exists_hom_pointClosure {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] (w : X) :
    ∃ q : X.pointClosure w ⟶ Y.pointClosure (p.base w),
      q ≫ Y.pointClosureι (p.base w) = X.pointClosureι w ≫ p := by
  set f := X.pointClosureι w ≫ p with hf
  have : IsIntegral f.image := f.isIntegral_image
  have h1 : f.toImage.base (genericPoint (X.pointClosure w)) = genericPoint f.image := by
    have h := (genericPoint_spec (X.pointClosure w)).image f.toImage.continuous
    rw [Set.image_univ, f.toImage.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec _)
  have hgen : f.imageι.base (genericPoint f.image) = p.base w := by
    rw [← h1, ← Scheme.Hom.comp_apply, f.toImage_imageι, hf, Scheme.Hom.comp_apply,
      Scheme.pointClosureι_genericPoint]
  obtain ⟨θ, hθ⟩ := exists_iso_pointClosure_of_isClosedImmersion f.imageι (p.base w) hgen
  exact ⟨f.toImage ≫ θ.hom, by rw [Category.assoc, hθ, f.toImage_imageι]⟩

/-- **Dimension drop kills the pulled-back divisor** (Stacks 02SU, proof, case `dim W' < dim W`):
`q : W → W'` proper dominant between integral schemes locally of finite type over `k`,
`dim W = d + 1 > dim W' = d'`, `N` a line bundle on `W'`, `s ≠ 0` a rational section of `N`. Then
`q_* div_{q^*N}(q^*s) = 0` as a cycle. Proof: a point `x` with `div(q^*s)(x) ≠ 0` has coheight `1`,
hence height `d` (Stacks 0A21); if moreover `height x = height (q x)` then `height (q x) = d ≥ d'`
forces `coheight (q x) = 0`, i.e. `q x = η_{W'}`; but at `x ↦ η_{W'}` the order of `q^*s` is the
order of the image of a unit of `O_{W',η}` (`rationalSectionOrd_rationalSectionPullback_of_generator`,
`ord_algebraMap_of_isUnit`), which is `0`. -/
theorem properPushforward_rationalSectionDivisor_pullback_eq_zero_of_lt {k : Type u} [Field k]
    {W W' : Scheme.{u}} [W.Over (Spec (CommRingCat.of k))] [W'.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (W' ↘ Spec (CommRingCat.of k))]
    [IsIntegral W] [IsIntegral W'] [IsLocallyNoetherian W] [IsLocallyNoetherian W']
    (q : W ⟶ W') [IsProper q] (hq : q.base (genericPoint W) = genericPoint W')
    {d d' : ℕ} (hW : topologicalKrullDim W = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hW' : topologicalKrullDim W' = (d' : WithBot ℕ∞)) (hlt : d' < d + 1)
    (N : W'.Modules) [N.IsLineBundle] (s : N.presheaf.stalk (genericPoint W')) (hs : s ≠ 0) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward q
      (((Scheme.Modules.pullback q).obj N).rationalSectionDivisor
        (Scheme.Modules.rationalSectionPullback q hq N s)) = 0 := by
  classical
  ext z
  rw [properPushforward_apply']
  show _ = (0 : ℤ)
  refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
  by_cases hdiv : ((Scheme.Modules.pullback q).obj N).rationalSectionDivisor
      (Scheme.Modules.rationalSectionPullback q hq N s) x = 0
  · rw [hdiv, zero_mul]
  by_cases hm : Order.height x = Order.height (q.base x)
  swap
  · unfold AlgebraicCycle.mapCoeff
    rw [if_neg hm]
    simp
  exfalso
  have hco : Order.coheight x = 1 := Scheme.Modules.rationalSectionDivisor_support _ _ x hdiv
  have hhx : Order.height x = (d : ℕ∞) :=
    Scheme.height_eq_of_coheight_eq_one (W ↘ Spec (CommRingCat.of k)) hW hco
  have hadd := height_add_coheight_eq_of_locallyOfFiniteType (k := k) W' d' hW' (q.base x)
  rw [← hm, hhx] at hadd
  have hco0 : Order.coheight (q.base x) = 0 := by
    by_contra hne
    have h1 : (1 : ℕ∞) ≤ Order.coheight (q.base x) := Order.one_le_iff_ne_zero.mpr hne
    have h2 : ((d + 1 : ℕ) : ℕ∞) ≤ (d' : ℕ∞) := by
      calc ((d + 1 : ℕ) : ℕ∞) = (d : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ (d : ℕ∞) + Order.coheight (q.base x) := by gcongr
        _ = (d' : ℕ∞) := hadd
    have : d + 1 ≤ d' := by exact_mod_cast h2
    omega
  have hqx : q.base x = genericPoint W' := by
    have hmax : IsMax (q.base x) := Order.coheight_eq_zero.mp hco0
    have h1 : genericPoint W' ⤳ q.base x := genericPoint_specializes _
    have h2 : q.base x ⤳ genericPoint W' := hmax h1
    exact (h2.antisymm h1).eq
  apply hdiv
  show ((Scheme.Modules.pullback q).obj N).rationalSectionOrd
    (Scheme.Modules.rationalSectionPullback q hq N s) x = 0
  obtain ⟨τ, hτ⟩ := Scheme.Modules.exists_stalk_generator N (q.base x)
  obtain ⟨γ, hγ⟩ := Scheme.Modules.exists_smul_toGenericFiber_eq N (q.base x) τ hτ s
  rw [Scheme.Modules.rationalSectionOrd_rationalSectionPullback_of_generator q hq N x τ hτ γ s hs hγ]
  let _ := functionFieldAlgebra q hq
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    exact hs (hγ.symm.trans (zero_smul _ _))
  have key : ∀ (y : W') (hy : y = genericPoint W') (γ : W'.functionField), γ ≠ 0 →
      ∃ u : W'.presheaf.stalk y, IsUnit u ∧
        algebraMap (W'.presheaf.stalk y) W'.functionField u = γ := by
    intro y hy γ hγ0
    subst hy
    refine ⟨γ, (Units.mk0 γ hγ0).isUnit, ?_⟩
    change (W'.presheaf.stalkSpecializes ((genericPoint_spec W').specializes trivial)).hom γ = γ
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  obtain ⟨u, hu, hγu⟩ := key (q.base x) hqx γ hγ0
  rw [← hγu, Scheme.Modules.functionFieldAlgebra_algebraMap_stalk q hq x u]
  exact Scheme.Modules.ord_algebraMap_of_isUnit x (hu.map (q.stalkMap x).hom)

/-- **Stacks 02SU, one point at a time.** For `w` of height `d + 1` with image `y = p w`,
`p_*(c_1(p^*L) ∩ [w]) − c_1(L) ∩ p_*[w]` is rationally trivial on `Y`, with witnesses supported in
`closure {y}`. Proof (Stacks 02SU): factor `ι_w ≫ p = q ≫ ι_y` with `q : W = closure{w} → W' = closure{y}`
proper dominant (`exists_hom_pointClosure`). Write `c_1(p^*L) ∩ [w] = ι_{w*} div(s)`, transport `s` to
`q^*N` (`N = ι_y^*L`), and compare with the pullback `q^*s'` of a rational section `s'` of `N`:
`div(s) = div(q^*s') + div(g)` (02SH). The term `ι_{y*} q_* div(g)` is rationally trivial by 02S2
(`properPushforward_rationallyEquivalent`, statement only) and lands in `closure{y}`. If
`height y = d + 1`: `q_* div(q^*s') = deg · div_N(s')` (02ST divisor level), `p_*[w] = deg·[y]`, and
`c_1(L) ∩ [y] = ι_{y*} div_N(s') + (principal cycles)` by 02SH and the closed-immersion case of 02SU
(`exists_firstChernCapPoint_sub_eq_principalCycle`). If `height y < d + 1`: `p_*[w] = 0` and
`q_* div(q^*s') = 0` (`properPushforward_rationalSectionDivisor_pullback_eq_zero_of_lt`). -/
theorem firstChernCapPoint_properPushforward_sub_mem {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [DecidableEq X] [DecidableEq Y]
    (p : X ⟶ Y) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    (L : Y.Modules) [L.IsLineBundle] (d : ℕ) (w : X)
    (hw : Order.height w = ((d + 1 : ℕ) : ℕ∞)) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward p (firstChernCapPoint ((Scheme.Modules.pullback p).obj L) w)
      - firstChernCapCycleAux L (d + 1)
          (AlgebraicGeometry.AlgebraicCycle.properPushforward p (Function.locallyFinsuppWithin.single w (1 : ℤ)))
      ∈ ratEquivZeroOn Y d (closure {p.base w}) := by
  obtain ⟨q, hq⟩ := exists_hom_pointClosure p w
  have hqι : IsProper (q ≫ Y.pointClosureι (p.base w)) := by rw [hq]; infer_instance
  have : IsProper q := IsProper.of_comp q (Y.pointClosureι (p.base w))
  have hqη : q.base (genericPoint (X.pointClosure w)) = genericPoint (Y.pointClosure (p.base w)) := by
    apply (Y.pointClosureι (p.base w)).isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply, Scheme.pointClosureι_genericPoint,
      Scheme.pointClosureι_genericPoint]
  -- k-structures on W = closure{w} and W' = closure{(p.base w)}
  let : (X.pointClosure w).Over (Spec (CommRingCat.of k)) :=
    ⟨X.pointClosureι w ≫ (X ↘ Spec (CommRingCat.of k))⟩
  let : (Y.pointClosure (p.base w)).Over (Spec (CommRingCat.of k)) :=
    ⟨Y.pointClosureι (p.base w) ≫ (Y ↘ Spec (CommRingCat.of k))⟩
  have : LocallyOfFiniteType ((X.pointClosure w) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (X.pointClosureι w ≫ (X ↘ Spec (CommRingCat.of k))))
  have : LocallyOfFiniteType ((Y.pointClosure (p.base w)) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (Y.pointClosureι (p.base w) ≫ (Y ↘ Spec (CommRingCat.of k))))
  have : q.IsOver (Spec (CommRingCat.of k)) := ⟨by
    change q ≫ (Y.pointClosureι (p.base w) ≫ (Y ↘ Spec (CommRingCat.of k))) =
      X.pointClosureι w ≫ (X ↘ Spec (CommRingCat.of k))
    rw [← Category.assoc, hq, Category.assoc, comp_over p]⟩
  -- dimensions
  have hWd : topologicalKrullDim (X.pointClosure w) = ((d + 1 : ℕ) : WithBot ℕ∞) :=
    Scheme.topologicalKrullDim_pointClosure w hw
  have hηW : Order.height (genericPoint (X.pointClosure w)) = ((d + 1 : ℕ) : ℕ∞) :=
    (Scheme.height_top_pointClosure w).trans hw
  have hyle : Order.height (p.base w) ≤ ((d + 1 : ℕ) : ℕ∞) :=
    hw ▸ Scheme.height_apply_le_of_specializingMap p p.isClosedMap.specializingMap w
  have hyne : Order.height (p.base w) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hyle
  obtain ⟨d', hd'⟩ : ∃ d' : ℕ, Order.height (p.base w) = (d' : ℕ∞) :=
    ⟨(Order.height (p.base w)).toNat, (ENat.natCast_toNat hyne).symm⟩
  have hW'd : topologicalKrullDim (Y.pointClosure (p.base w)) = (d' : WithBot ℕ∞) :=
    Scheme.topologicalKrullDim_pointClosure (p.base w) hd'
  have hηW' : Order.height (genericPoint (Y.pointClosure (p.base w))) = (d' : ℕ∞) :=
    (Scheme.height_top_pointClosure (p.base w)).trans hd'
  -- rational sections
  set N := (Scheme.Modules.pullback (Y.pointClosureι (p.base w))).obj L with hN
  obtain ⟨s, hs, hcap⟩ := exists_firstChernCapPoint_eq ((Scheme.Modules.pullback p).obj L) w
  let φ : (Scheme.Modules.pullback (X.pointClosureι w)).obj ((Scheme.Modules.pullback p).obj L) ≅
      (Scheme.Modules.pullback q).obj N :=
    (Scheme.Modules.pullbackComp (X.pointClosureι w) p).app L ≪≫
      (Scheme.Modules.pullbackCongr hq.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp q (Y.pointClosureι (p.base w))).app L).symm
  have hs₂ := moduleStalkMap_iso_ne_zero φ _ s hs
  have hdiv := rationalSectionDivisor_iso φ s hs
  obtain ⟨s', hs'⟩ := Scheme.Modules.exists_stalk_genericPoint_ne_zero N
  set t : ((Scheme.Modules.pullback q).obj N).stalk (genericPoint (X.pointClosure w)) :=
    Scheme.Modules.rationalSectionPullback q hqη N s' with ht_def
  have ht : t ≠ 0 := Scheme.Modules.rationalSectionPullback_ne_zero q hqη N s' hs'
  have := Classical.decEq (X.pointClosure w)
  have := Classical.decEq (Y.pointClosure (p.base w))
  obtain ⟨g, hg⟩ := exists_rationalSectionDivisor_eq_add_principalCycle
    ((Scheme.Modules.pullback q).obj N) _ _ hs₂ ht
  have hpush : AlgebraicGeometry.AlgebraicCycle.properPushforward p
      (firstChernCapPoint ((Scheme.Modules.pullback p).obj L) w) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward (Y.pointClosureι (p.base w)) (AlgebraicGeometry.AlgebraicCycle.properPushforward q
        (((Scheme.Modules.pullback q).obj N).rationalSectionDivisor t)) +
      AlgebraicGeometry.AlgebraicCycle.properPushforward (Y.pointClosureι (p.base w)) (AlgebraicGeometry.AlgebraicCycle.properPushforward q
        ((X.pointClosure w).principalCycle g)) := by
    rw [hcap, pp_comp, ← properPushforward_congr hq, ← pp_comp, hdiv, hg, pp_add, pp_add]
  -- the principal part: rationally trivial by Stacks 02S2 (statement) and the closed immersion ι_y
  have hG : AlgebraicGeometry.AlgebraicCycle.properPushforward (Y.pointClosureι (p.base w)) (AlgebraicGeometry.AlgebraicCycle.properPushforward q
      ((X.pointClosure w).principalCycle g)) ∈ ratEquivZeroOn Y d (closure {(p.base w)}) := by
    apply properPushforward_pointClosure_mem_ratEquivZeroOn (p.base w) d
    have hpr : (X.pointClosure w).principalCycle g ∈ cycleSubgroup (X.pointClosure w) d :=
      Scheme.principalCycle_mem_cycleSubgroup ((X.pointClosure w) ↘ Spec (CommRingCat.of k)) hWd g
    obtain ⟨-, -, h⟩ := AlgebraicCycle.properPushforward_rationallyEquivalent (k := k) q d
      ((X.pointClosure w).principalCycle g) 0 ⟨hpr, zero_mem _, by
        rw [sub_zero]; exact single_mem_ratEquivZero (isRatEquivGen_principalCycle hηW g)⟩
    simpa only [pp_zero, sub_zero] using h
  rw [hpush]
  by_cases hcase : Order.height (p.base w) = ((d + 1 : ℕ) : ℕ∞)
  · -- same dimension: Stacks 02ST at the divisor level
    have hd'eq : d' = d + 1 := by exact_mod_cast hd'.symm.trans hcase
    subst hd'eq
    have h02st : AlgebraicGeometry.AlgebraicCycle.properPushforward q
        (((Scheme.Modules.pullback q).obj N).rationalSectionDivisor t) =
        (functionFieldDegree q : ℤ) • N.rationalSectionDivisor s' :=
      Scheme.Modules.properPushforward_rationalSectionDivisor_pullback q hqη (k := k)
        (d + 1) hWd hW'd N s' hs'
    have hsingle : AlgebraicGeometry.AlgebraicCycle.properPushforward p (Function.locallyFinsuppWithin.single w (1 : ℤ))
        = Function.locallyFinsuppWithin.single (p.base w) (functionFieldDegree q : ℤ) := by
      have h1 : Function.locallyFinsuppWithin.single w (1 : ℤ) =
          AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
            (Function.locallyFinsuppWithin.single (genericPoint (X.pointClosure w)) (1 : ℤ)) := by
        rw [properPushforward_single_of_isClosedImmersion, Scheme.pointClosureι_genericPoint]
      rw [h1, pp_comp, ← properPushforward_congr hq, ← pp_comp, properPushforward_single q,
        properPushforward_single_of_isClosedImmersion, hqη, Scheme.pointClosureι_genericPoint]
      congr 1
      unfold AlgebraicCycle.mapCoeff
      rw [if_pos (by rw [hqη, hηW, hηW']), one_mul]
      rfl
    rw [hsingle, firstChernCapCycleAux_single, if_pos hcase]
    obtain ⟨g₁, hg₁⟩ := exists_firstChernCapPoint_sub_eq_principalCycle L (p.base w)
      (genericPoint (Y.pointClosure (p.base w)))
    obtain ⟨s₅, hs₅, h5⟩ := firstChernCapPoint_genericPoint N
    obtain ⟨g₄, hg₄⟩ := exists_rationalSectionDivisor_eq_add_principalCycle N s₅ s' hs₅ hs'
    have hy' : (Y.pointClosureι (p.base w)).base (genericPoint (Y.pointClosure (p.base w))) = (p.base w) :=
      Scheme.pointClosureι_genericPoint (p.base w)
    have hB : firstChernCapPoint L (p.base w) =
        AlgebraicGeometry.AlgebraicCycle.properPushforward (Y.pointClosureι (p.base w)) (N.rationalSectionDivisor s') +
        AlgebraicGeometry.AlgebraicCycle.properPushforward (Y.pointClosureι (p.base w)) ((Y.pointClosure (p.base w)).principalCycle g₄) +
        AlgebraicGeometry.AlgebraicCycle.properPushforward
          (Y.pointClosureι ((Y.pointClosureι (p.base w)).base (genericPoint (Y.pointClosure (p.base w)))))
          ((Y.pointClosure ((Y.pointClosureι (p.base w)).base (genericPoint (Y.pointClosure (p.base w))))).principalCycle
            g₁) := by
      have e : firstChernCapPoint L (p.base w) =
          firstChernCapPoint L ((Y.pointClosureι (p.base w)).base (genericPoint (Y.pointClosure (p.base w)))) := by
        rw [hy']
      rw [e, sub_eq_iff_eq_add.mp hg₁, h5, hg₄, pp_add]
      abel
    have hgen₁ : AlgebraicGeometry.AlgebraicCycle.properPushforward
        (Y.pointClosureι ((Y.pointClosureι (p.base w)).base (genericPoint (Y.pointClosure (p.base w)))))
        ((Y.pointClosure ((Y.pointClosureι (p.base w)).base (genericPoint (Y.pointClosure (p.base w))))).principalCycle
          g₁) ∈ ratEquivZeroOn Y d (closure {(p.base w)}) :=
      single_mem_ratEquivZeroOn (by rw [hy']; exact subset_closure rfl)
        ⟨by rw [hy']; exact hcase, inferInstance, inferInstance, inferInstance, g₁, rfl⟩
    have hgen₄ : AlgebraicGeometry.AlgebraicCycle.properPushforward (Y.pointClosureι (p.base w))
        ((Y.pointClosure (p.base w)).principalCycle g₄) ∈ ratEquivZeroOn Y d (closure {(p.base w)}) :=
      single_mem_ratEquivZeroOn (subset_closure rfl)
        ⟨hcase, inferInstance, inferInstance, inferInstance, g₄, rfl⟩
    rw [h02st, pp_zsmul, hB]
    have key : ∀ (A G B C : AlgebraicCycle Y ℤ) (n : ℤ),
        n • A + G - n • (A + B + C) = G - n • B - n • C := by
      intros; rw [smul_add, smul_add]; abel
    rw [key]
    exact sub_mem (sub_mem hG (zsmul_mem hgen₄ _)) (zsmul_mem hgen₁ _)
  · -- dimension drop: both remaining terms vanish
    have hlt : d' < d + 1 := by
      have := lt_of_le_of_ne hyle hcase
      rw [hd'] at this
      exact_mod_cast this
    have hvan : AlgebraicGeometry.AlgebraicCycle.properPushforward q
        (((Scheme.Modules.pullback q).obj N).rationalSectionDivisor t) = 0 :=
      properPushforward_rationalSectionDivisor_pullback_eq_zero_of_lt (k := k) q hqη
        hWd hW'd hlt N s' hs'
    have hsingle0 : AlgebraicGeometry.AlgebraicCycle.properPushforward p
        (Function.locallyFinsuppWithin.single w (1 : ℤ)) = 0 := by
      have hm0 : AlgebraicCycle.mapCoeff p (Order.height (α := X)) (Order.height (α := Y)) w = 0 := by
        unfold AlgebraicCycle.mapCoeff
        rw [if_neg]
        rw [hw]
        exact fun h => hcase h.symm
      rw [properPushforward_single p, hm0, Nat.cast_zero, mul_zero,
        Function.locallyFinsuppWithin.single_zero]
      rfl
    rw [hvan, pp_zero, zero_add,
      hsingle0, firstChernCapCycleAux_zero, sub_zero]
    exact hG

end MiyaokaMori.Stacks02suCycle

/-- The cycle-level core of Stacks 02SU. The geometric reduction is isolated here so that
the closed-chain algebra below is explicit and independently compilable. -/
private theorem firstChernCapCycleAux_projection_sub_mem_ratEquivZero
    {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    [AlgebraicGeometry.IsLocallyNoetherian Y]
    (p : X ⟶ Y) [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper p]
    (L : Y.Modules) [L.IsLineBundle] (d : ℕ)
    (α : AlgebraicGeometry.AlgebraicCycle X ℤ)
    (hα : α ∈ AlgebraicGeometry.cycleSubgroup X (d + 1)) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward p
          (AlgebraicGeometry.firstChernCapCycleAux
            ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1) α)
        - AlgebraicGeometry.firstChernCapCycleAux L (d + 1)
            (AlgebraicGeometry.AlgebraicCycle.properPushforward p α)
      ∈ AlgebraicGeometry.ratEquivZero Y d := by
  classical
  open MiyaokaMori.Stacks02suCycle in
  set S : Set X := {w : X | Order.height w = ((d + 1 : ℕ) : ℕ∞) ∧ α w ≠ 0} with hS
  have hlfS : AlgebraicGeometry.LocallyFinitePoints (fun j : S => (j : X)) :=
    AlgebraicGeometry.locallyFinitePoints_of_subset_support α (fun w hw => hw.2)
  have hlfp : AlgebraicGeometry.LocallyFinitePoints (fun j : S => p.base (j : X)) :=
    MiyaokaMori.Stacks02suCycle.locallyFinitePoints_comp_of_quasiCompact p hlfS
  set Lp := (AlgebraicGeometry.Scheme.Modules.pullback p).obj L with hLp
  let D : S → AlgebraicGeometry.AlgebraicCycle Y ℤ := fun j =>
    AlgebraicGeometry.AlgebraicCycle.properPushforward p (AlgebraicGeometry.firstChernCapPoint Lp (j : X)) -
      AlgebraicGeometry.firstChernCapCycleAux L (d + 1)
        (AlgebraicGeometry.AlgebraicCycle.properPushforward p (Function.locallyFinsuppWithin.single (j : X) (1 : ℤ)))
  refine AlgebraicGeometry.ratEquivZero_of_locallyFinite_sum (fun j : S => closure {p.base (j : X)})
    ((AlgebraicGeometry.locallyFinitePoints_iff_locallyFinite_closure _).mp hlfp) _
    (fun j => α (j : X) • D j)
    (fun j => (AlgebraicGeometry.ratEquivZeroOn Y d _).zsmul_mem
      (MiyaokaMori.Stacks02suCycle.firstChernCapPoint_properPushforward_sub_mem (k := k) p L d
        (j : X) j.2.1) _) ?_
  intro z
  have hsupA : ∀ (j : S) (t : X),
      (α (j : X) • AlgebraicGeometry.firstChernCapPoint Lp (j : X)) t ≠ 0 → (j : X) ⤳ t :=
    fun j t ht => AlgebraicGeometry.firstChernCapPoint_specializes Lp
      (right_ne_zero_of_mul (by rwa [AlgebraicGeometry.AlgebraicCycle.zsmul_apply] at ht))
  have hA : AlgebraicGeometry.AlgebraicCycle.properPushforward p (AlgebraicGeometry.firstChernCapCycleAux Lp (d + 1) α) z =
      ∑ᶠ j : S, AlgebraicGeometry.AlgebraicCycle.properPushforward p
        (α (j : X) • AlgebraicGeometry.firstChernCapPoint Lp (j : X)) z :=
    MiyaokaMori.Stacks02suCycle.properPushforward_of_locallyFiniteSum p hlfS hsupA _ (fun t => by
      rw [MiyaokaMori.Stacks02suCycle.firstChernCapCycleAux_apply_eq_finsum_subtype]
      exact finsum_congr fun j => (AlgebraicGeometry.AlgebraicCycle.zsmul_apply _ _ _).symm) z
  have hsup1 : ∀ (j : S) (t : X),
      (α (j : X) • Function.locallyFinsuppWithin.single (j : X) (1 : ℤ)) t ≠ 0 → (j : X) ⤳ t := by
    intro j t ht
    rw [AlgebraicGeometry.AlgebraicCycle.zsmul_apply, Function.locallyFinsuppWithin.single_apply] at ht
    split_ifs at ht with h
    · exact specializes_of_eq h.symm
    · exact absurd (mul_zero _) ht
  have hpα : ∀ t, AlgebraicGeometry.AlgebraicCycle.properPushforward p α t =
      ∑ᶠ j : S, (α (j : X) • AlgebraicGeometry.AlgebraicCycle.properPushforward p
        (Function.locallyFinsuppWithin.single (j : X) (1 : ℤ))) t := fun t => by
    rw [MiyaokaMori.Stacks02suCycle.properPushforward_of_locallyFiniteSum p hlfS hsup1 α
      (MiyaokaMori.Stacks02suCycle.apply_eq_finsum_single_subtype (d + 1) α hα) t]
    exact finsum_congr fun j => by rw [MiyaokaMori.Stacks02suCycle.pp_zsmul]
  have hsupB : ∀ (j : S) (t : Y), (α (j : X) • AlgebraicGeometry.AlgebraicCycle.properPushforward p
      (Function.locallyFinsuppWithin.single (j : X) (1 : ℤ))) t ≠ 0 → p.base (j : X) ⤳ t := by
    intro j t ht
    rw [AlgebraicGeometry.AlgebraicCycle.zsmul_apply] at ht
    obtain ⟨x, hx, hne⟩ := MiyaokaMori.Stacks02suCycle.exists_of_properPushforward_apply_ne_zero p _
      (right_ne_zero_of_mul ht)
    rw [Function.locallyFinsuppWithin.single_apply] at hne
    split_ifs at hne with h
    · rw [← hx, h]
    · exact absurd rfl hne
  have hB : AlgebraicGeometry.firstChernCapCycleAux L (d + 1) (AlgebraicGeometry.AlgebraicCycle.properPushforward p α) z =
      ∑ᶠ j : S, AlgebraicGeometry.firstChernCapCycleAux L (d + 1)
        (α (j : X) • AlgebraicGeometry.AlgebraicCycle.properPushforward p
          (Function.locallyFinsuppWithin.single (j : X) (1 : ℤ))) z :=
    AlgebraicGeometry.firstChernCapCycleAux_of_locallyFiniteSum L (d + 1) hlfp hsupB _ hpα z
  have hfinA : (Function.support fun j : S => AlgebraicGeometry.AlgebraicCycle.properPushforward p
      (α (j : X) • AlgebraicGeometry.firstChernCapPoint Lp (j : X)) z).Finite :=
    AlgebraicGeometry.finite_support_of_locallyFinitePoints hlfp _ (fun j t ht => by
      obtain ⟨x, hx, hne⟩ := MiyaokaMori.Stacks02suCycle.exists_of_properPushforward_apply_ne_zero p _ ht
      exact hx ▸ (hsupA j x hne).map p.continuous) z
  have hfinB : (Function.support fun j : S => AlgebraicGeometry.firstChernCapCycleAux L (d + 1)
      (α (j : X) • AlgebraicGeometry.AlgebraicCycle.properPushforward p
        (Function.locallyFinsuppWithin.single (j : X) (1 : ℤ))) z).Finite :=
    AlgebraicGeometry.finite_support_of_locallyFinitePoints hlfp _ (fun j t ht => by
      obtain ⟨y', hy', hspec⟩ :=
        MiyaokaMori.Stacks02suCycle.exists_of_firstChernCapCycleAux_apply_ne_zero L (d + 1) _ ht
      exact (hsupB j y' hy').trans hspec) z
  show AlgebraicGeometry.AlgebraicCycle.properPushforward p (AlgebraicGeometry.firstChernCapCycleAux Lp (d + 1) α) z -
    AlgebraicGeometry.firstChernCapCycleAux L (d + 1) (AlgebraicGeometry.AlgebraicCycle.properPushforward p α) z = _
  rw [hA, hB, ← finsum_sub_distrib hfinA hfinB]
  refine finsum_congr fun j => ?_
  rw [MiyaokaMori.Stacks02suCycle.pp_zsmul, MiyaokaMori.Stacks02suCycle.firstChernCapCycleAux_zsmul]
  simp only [AlgebraicGeometry.AlgebraicCycle.zsmul_apply]
  rw [← mul_sub]
  rfl

theorem AlgebraicGeometry.chowPushforward_firstChernCapCycle_pullback {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y]
    (p : X ⟶ Y) [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper p]
    (L : Y.Modules) [L.IsLineBundle] (d : ℕ) (α : AlgebraicGeometry.AlgebraicCycle X ℤ)
    (hα : α ∈ AlgebraicGeometry.cycleSubgroup X (d + 1)) :
    AlgebraicGeometry.chowPushforward p d
        (AlgebraicGeometry.firstChernCapCycle (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X)
          ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1) α)
      = AlgebraicGeometry.firstChernCapCycle (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) Y)
          L (d + 1) (AlgebraicGeometry.AlgebraicCycle.properPushforward p α) := by
  let hdesc : AlgebraicGeometry.PushforwardDescends p d :=
    AlgebraicGeometry.AlgebraicCycle.properPushforward_rationallyEquivalent
      (k := k) p d
  let hX := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over
    (k := k) X
  let hY := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over
    (k := k) Y
  let a := AlgebraicGeometry.firstChernCapCycleAux
    ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1) α
  let b := AlgebraicGeometry.firstChernCapCycleAux L (d + 1)
    (AlgebraicGeometry.AlgebraicCycle.properPushforward p α)
  have ha : a ∈ AlgebraicGeometry.cycleSubgroup X d :=
    AlgebraicGeometry.firstChernCapCycleAux_mem hX _ (d + 1) α
  have hpa : AlgebraicGeometry.AlgebraicCycle.properPushforward p a ∈
      AlgebraicGeometry.cycleSubgroup Y d :=
    AlgebraicGeometry.properPushforward_mem_cycleSubgroup p d hdesc ⟨a, ha⟩
  have hb : b ∈ AlgebraicGeometry.cycleSubgroup Y d :=
    AlgebraicGeometry.firstChernCapCycleAux_mem hY L (d + 1)
      (AlgebraicGeometry.AlgebraicCycle.properPushforward p α)
  have hpush : AlgebraicGeometry.chowPushforward p d
      (AlgebraicGeometry.firstChernCapCycle hX
        ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1) α) =
      AlgebraicGeometry.ChowGroup.mk ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward p a, hpa⟩ := by
    have hcp : AlgebraicGeometry.chowPushforward p d =
        QuotientAddGroup.map _ _
          (AlgebraicGeometry.cyclePushforwardHom p d hdesc)
          (AlgebraicGeometry.cyclePushforwardHom_rel p d hdesc) := by
      unfold AlgebraicGeometry.chowPushforward
      exact dif_pos hdesc
    rw [hcp]
    rfl
  rw [hpush]
  change AlgebraicGeometry.ChowGroup.mk ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward p a, hpa⟩ =
    AlgebraicGeometry.ChowGroup.mk ⟨b, hb⟩
  rw [← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  exact firstChernCapCycleAux_projection_sub_mem_ratEquivZero
    (k := k) (X := X) (Y := Y) p L d α hα

end
