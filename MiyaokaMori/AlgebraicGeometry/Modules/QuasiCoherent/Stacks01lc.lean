import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforwardQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization

/-! # Pushforward along a quasi-compact quasi-separated morphism preserves quasi-coherence (Stacks 01LC)

The pushforward of a quasi-coherent module along a quasi-compact quasi-separated morphism is
quasi-coherent; in particular pushforward along affine and finite morphisms preserves quasi-coherence.

Source: Stacks 01LC.

## Proof

Instead of the equalizer/Čech description we use the *qcqs lemma* for sections
of quasi-coherent modules (Stacks 01P7 / Vakil "qcqs lemma"; the module version of Mathlib's
`isLocalization_basicOpen_of_qcqs`) together with Mathlib's characterization of quasi-coherence on an
affine scheme by localization (`isQuasicoherent_iff_isIso_fromTildeΓ`, `isIso_fromTildeΓ_iff_isLocalizing`).

1. **qcqs lemma for modules** (`Stacks01lcAux`). `X` a scheme, `M` quasi-coherent, `s ∈ Γ(X, O_X)`,
   `V ⊆ X` a quasi-compact open, `B V := X.basicOpen (s|_V) = V ∩ X_s`.
   * *Uniqueness* (`exists_pow_smul_eq_zero_of_isCompact`, needs only `V` quasi-compact):
     `t ∈ Γ(V, M)`, `t|_{B V} = 0 ⇒ ∃ n, s^n t = 0`. Induction on a finite affine cover
     (`compact_open_induction_on`): on an affine open this is `exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero`
     (Stacks 01I8 / 01IB, module `QcSectionsBasicOpenLocalization`); for `S ∪ U` take the sum of the two
     exponents and use the sheaf property (`eq_of_locally_eq₂`).
   * *Existence* (`exists_pow_smul_eq_map_of_isCompact`, needs `X` quasi-separated):
     `y ∈ Γ(B V, M) ⇒ ∃ n, t ∈ Γ(V, M)`, `t|_{B V} = s^n y`. Same induction; for `S ∪ U` (`U` affine):
     get `t₁` on `S` with exponent `n₁`, `t₂` on `U` with exponent `n₂`; `S ∩ U` is quasi-compact
     (quasi-separated), and `s^{n₂} t₁ − s^{n₁} t₂` restricts to `0` on `B (S ∩ U)`, so by uniqueness
     `s^m (s^{n₂} t₁ − s^{n₁} t₂) = 0` on `S ∩ U`; glue `s^{m+n₂} t₁` and `s^{m+n₁} t₂` to `t` on `S ∪ U`
     (`existsUnique_gluing'`), and check `t|_{B(S ∪ U)} = s^{m+n₁+n₂} y` on the cover `{B S, B U}`.
2. **Affine base `Spec R`** (`isQuasicoherent_pushforward_spec`): `g : X → Spec R` with `X` quasi-compact
   and quasi-separated. `g_*M` is quasi-coherent iff for every `r ∈ R` the restriction
   `Γ(Spec R, g_*M) → Γ(D(r), g_*M)` is the localization at `r` (`IsLocalizing`). Now
   `Γ(D(r), g_*M) = Γ(g⁻¹D(r), M)`, `g⁻¹D(r) = X_s` with `s = g^♯(r)` (`preimage_basicOpen_top`,
   `basicOpen_eq_of_affine`), and `r` acts on these sections through `s` (`smul_Spec_def`, naturality of
   `g^♯`). The three axioms of `IsLocalizedModule.Away.mk_of_addCommGroup` are: `r` acts invertibly on
   `Γ(D(r), -)` (Mathlib `isUnit_algebraMap_end_of_le_basicOpen`), existence and uniqueness from step 1.
3. **Affine base in general** (`isQuasicoherent_pushforward_of_isAffine_target`): transport along
   `Y.isoSpec` (`pushforwardComp`, `AffineTilde.isQuasicoherent_pushforward_hom`).
4. **General target** (`isQuasicoherent_pushforward`): quasi-coherence is affine-local on `Y`
   (`AffinePushforwardAux.isQuasicoherent_of_affineOpens_restrict`); for `V ⊆ Y` affine open,
   `(f_*M)|_V ≅ (f|_{f⁻¹V})_*(M|_{f⁻¹V})` (`pushforwardRestrictIso`), `f⁻¹V` is quasi-compact
   (`QuasiCompact`) and quasi-separated (`Scheme.Hom.isQuasiSeparated_preimage`), so step 3 applies.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.Stacks01lcAux

open AlgebraicGeometry

variable {X : Scheme.{u}} (M : X.Modules) (s : Γ(X, ⊤))

/-- `s|_V`. -/
abbrev rs (V : X.Opens) : Γ(X, V) := X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s

/-- `B V = V ∩ X_s`, written as the basic open of `s|_V`. -/
abbrev B (V : X.Opens) : X.Opens := X.basicOpen (rs s V)

theorem B_eq (V : X.Opens) : B s V = V ⊓ X.basicOpen s := X.basicOpen_res _ _

theorem B_le (V : X.Opens) : B s V ≤ V := X.basicOpen_le _

theorem B_mono {V W : X.Opens} (h : V ≤ W) : B s V ≤ B s W := by
  rw [B_eq, B_eq]; exact inf_le_inf_right _ h

theorem rs_res {V W : X.Opens} (h : W ≤ V) : X.presheaf.map (homOfLE h).op (rs s V) = rs s W := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

theorem res_res {V W Z : X.Opens} (h1 : W ≤ V) (h2 : Z ≤ W) (h3 : Z ≤ V) (t : Γ(M, V)) :
    M.presheaf.map (homOfLE h2).op (M.presheaf.map (homOfLE h1).op t) =
      M.presheaf.map (homOfLE h3).op t := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

/-- Sections over an open contained in `⊥` are all equal (sheaf condition for the empty cover). -/
theorem eq_of_le_bot {V : X.Opens} (hV : V ≤ ⊥) (a b : Γ(M, V)) : a = b :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ (fun i : PEmpty.{u + 1} => i.elim)
    V (fun i => i.elim) (hV.trans bot_le) a b (fun i => i.elim)

/-- Gluing two sections of a sheaf of modules over `S ⊔ U`. -/
theorem exists_glue_pair (S U : X.Opens) (a : Γ(M, S)) (b : Γ(M, U))
    (h : M.presheaf.map (homOfLE (inf_le_left : S ⊓ U ≤ S)).op a =
      M.presheaf.map (homOfLE (inf_le_right : S ⊓ U ≤ U)).op b) :
    ∃ t : Γ(M, S ⊔ U), M.presheaf.map (homOfLE le_sup_left).op t = a ∧
      M.presheaf.map (homOfLE le_sup_right).op t = b := by
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let W : Bool → X.Opens := fun i => Bool.rec U S i
  let sf : ∀ i : Bool, Γ(M, W i) := fun i => Bool.rec (motive := fun i => Γ(M, W i)) b a i
  have hcover : S ⊔ U ≤ iSup W := sup_le (le_iSup W true) (le_iSup W false)
  have hcompat : TopCat.Presheaf.IsCompatible F.1 W sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · change M.presheaf.map (homOfLE (inf_le_left : U ⊓ S ≤ U)).op b =
        M.presheaf.map (homOfLE (inf_le_right : U ⊓ S ≤ S)).op a
      have := congrArg (M.presheaf.map (homOfLE (inf_comm U S).le).op) h
      rw [res_res M _ _ inf_le_right, res_res M _ _ inf_le_left] at this
      exact this.symm
    · exact h
    · rfl
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' W (S ⊔ U)
    (fun i => homOfLE (by cases i <;> simp [W])) hcover sf hcompat
  exact ⟨t, ht true, ht false⟩

variable [M.IsQuasicoherent]

/-- Uniqueness half of the qcqs lemma for modules (Stacks 01P7): on a quasi-compact open `V`, a section
of the quasi-coherent module `M` vanishing on `V ∩ X_s` is killed by a power of `s`. -/
theorem exists_pow_smul_eq_zero_of_isCompact (V : X.Opens) (hV : IsCompact (V : Set X)) :
    ∀ t : Γ(M, V), M.presheaf.map (homOfLE (B_le s V)).op t = 0 → ∃ n : ℕ, rs s V ^ n • t = 0 := by
  refine compact_open_induction_on (P := fun V => ∀ t : Γ(M, V),
    M.presheaf.map (homOfLE (B_le s V)).op t = 0 → ∃ n : ℕ, rs s V ^ n • t = 0) V hV ?_ ?_
  · intro t _
    exact ⟨0, eq_of_le_bot M le_rfl _ _⟩
  · intro S _ U ih t ht
    have h1 : M.presheaf.map (homOfLE (B_le s S)).op (M.presheaf.map (homOfLE le_sup_left).op t) = 0 := by
      rw [res_res M _ _ ((B_mono s le_sup_left).trans (B_le s (S ⊔ U.1))),
        ← res_res M (B_le s (S ⊔ U.1)) (B_mono s le_sup_left), ht, map_zero]
    have h2 : M.presheaf.map (homOfLE (X.basicOpen_le (rs s U.1))).op
        (M.presheaf.map (homOfLE le_sup_right).op t) = 0 := by
      rw [res_res M _ _ ((B_mono s le_sup_right).trans (B_le s (S ⊔ U.1))),
        ← res_res M (B_le s (S ⊔ U.1)) (B_mono s le_sup_right), ht, map_zero]
    obtain ⟨n₁, hn₁⟩ := ih _ h1
    obtain ⟨n₂, hn₂⟩ := exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero M U.2 (rs s U.1) _ h2
    refine ⟨n₁ + n₂, ?_⟩
    refine TopCat.Sheaf.eq_of_locally_eq₂ (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
      (homOfLE (le_sup_left : S ≤ S ⊔ U.1)) (homOfLE (le_sup_right : U.1 ≤ S ⊔ U.1)) le_rfl _ _ ?_ ?_
    · change M.presheaf.map _ (rs s (S ⊔ U.1) ^ (n₁ + n₂) • t) = M.presheaf.map _ (0 : Γ(M, S ⊔ U.1))
      rw [map_zero, map_smul, map_pow, rs_res, pow_add, mul_comm, mul_smul, hn₁, smul_zero]
    · change M.presheaf.map _ (rs s (S ⊔ U.1) ^ (n₁ + n₂) • t) = M.presheaf.map _ (0 : Γ(M, S ⊔ U.1))
      rw [map_zero, map_smul, map_pow, rs_res, pow_add, mul_smul, hn₂, smul_zero]

/-- Existence half of the qcqs lemma for modules (Stacks 01P7): on a quasi-compact open `V` of a
quasi-separated scheme, every section of `M` over `V ∩ X_s` extends to `V` after multiplication by a power
of `s`. -/
theorem exists_pow_smul_eq_map_of_isCompact [QuasiSeparatedSpace X] (V : X.Opens)
    (hV : IsCompact (V : Set X)) :
    ∀ y : Γ(M, B s V), ∃ (n : ℕ) (t : Γ(M, V)),
      M.presheaf.map (homOfLE (B_le s V)).op t = rs s (B s V) ^ n • y := by
  refine compact_open_induction_on (P := fun V => ∀ y : Γ(M, B s V), ∃ (n : ℕ) (t : Γ(M, V)),
    M.presheaf.map (homOfLE (B_le s V)).op t = rs s (B s V) ^ n • y) V hV ?_ ?_
  · intro y
    exact ⟨0, 0, eq_of_le_bot M (B_le s ⊥) _ _⟩
  · intro S hS U ih y
    obtain ⟨n₁, t₁, ht₁⟩ := ih (M.presheaf.map (homOfLE (B_mono s le_sup_left)).op y)
    obtain ⟨n₂, t₂, ht₂⟩ := exists_pow_smul_eq_map_basicOpen M U.2 (rs s U.1)
      (M.presheaf.map (homOfLE (B_mono s le_sup_right)).op y)
    rw [rs_res] at ht₂
    have hSU : IsCompact ((S ⊓ U.1 : X.Opens) : Set X) :=
      QuasiSeparatedSpace.inter_isCompact _ _ S.2 hS U.1.2 U.2.isCompact
    -- the two candidates agree on `B (S ⊓ U)` after multiplying by `s^{n₂}` resp. `s^{n₁}`
    have hab : M.presheaf.map (homOfLE (B_le s (S ⊓ U.1))).op
        (rs s (S ⊓ U.1) ^ n₂ • M.presheaf.map (homOfLE inf_le_left).op t₁ -
          rs s (S ⊓ U.1) ^ n₁ • M.presheaf.map (homOfLE inf_le_right).op t₂) = 0 := by
      rw [map_sub, sub_eq_zero, map_smul, map_smul, map_pow, map_pow, rs_res,
        res_res M _ _ ((B_le s (S ⊓ U.1)).trans inf_le_left),
        res_res M _ _ ((B_le s (S ⊓ U.1)).trans inf_le_right),
        ← res_res M (B_le s S) (B_mono s inf_le_left),
        ← res_res M (B_le s U.1) (B_mono s inf_le_right), ht₁, ht₂,
        map_smul, map_smul, map_pow, map_pow, rs_res, rs_res, smul_smul, smul_smul, ← pow_add,
        ← pow_add, add_comm,
        res_res M _ _ ((B_mono s inf_le_left).trans (B_mono s le_sup_left)),
        res_res M _ _ ((B_mono s inf_le_right).trans (B_mono s le_sup_right))]
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero_of_isCompact M s (S ⊓ U.1) hSU _ hab
    rw [smul_sub, sub_eq_zero, smul_smul, smul_smul, ← pow_add, ← pow_add] at hm
    have hglue : M.presheaf.map (homOfLE (inf_le_left : S ⊓ U.1 ≤ S)).op (rs s S ^ (m + n₂) • t₁) =
        M.presheaf.map (homOfLE (inf_le_right : S ⊓ U.1 ≤ U.1)).op (rs s U.1 ^ (m + n₁) • t₂) := by
      rw [map_smul, map_smul, map_pow, map_pow, rs_res, rs_res]
      exact hm
    obtain ⟨t, ht1, ht2⟩ := exists_glue_pair M S U.1 _ _ hglue
    refine ⟨m + n₁ + n₂, t, ?_⟩
    have hcover : B s (S ⊔ U.1) ≤ B s S ⊔ B s U.1 := by
      rw [B_eq, B_eq, B_eq]; exact (inf_sup_right _ _ _).le
    refine TopCat.Sheaf.eq_of_locally_eq₂ (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
      (homOfLE (B_mono s (le_sup_left : S ≤ S ⊔ U.1)))
      (homOfLE (B_mono s (le_sup_right : U.1 ≤ S ⊔ U.1))) hcover _ _ ?_ ?_
    · change M.presheaf.map _ (M.presheaf.map _ t) =
        M.presheaf.map _ (rs s (B s (S ⊔ U.1)) ^ (m + n₁ + n₂) • y)
      rw [res_res M _ _ ((B_le s S).trans le_sup_left), ← res_res M le_sup_left (B_le s S), ht1,
        map_smul, map_smul, map_pow, map_pow, rs_res, rs_res, ht₁, smul_smul, ← pow_add]
      congr 2
      omega
    · change M.presheaf.map _ (M.presheaf.map _ t) =
        M.presheaf.map _ (rs s (B s (S ⊔ U.1)) ^ (m + n₁ + n₂) • y)
      rw [res_res M _ _ ((B_le s U.1).trans le_sup_right), ← res_res M le_sup_right (B_le s U.1), ht2,
        map_smul, map_smul, map_pow, map_pow, rs_res, rs_res, ht₂, smul_smul, ← pow_add]

theorem rs_top : rs s ⊤ = s := by
  have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
  change X.presheaf.map (homOfLE le_top).op s = s
  rw [this, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The qcqs lemma (existence) for `V = ⊤`, with the basic open `X_s` given as any open equal to it. -/
theorem exists_pow_smul_eq_map_top [CompactSpace X] [QuasiSeparatedSpace X] {W : X.Opens}
    (hW : W = X.basicOpen s) (y : Γ(M, W)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)), M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s ^ n • y := by
  have hW' : W = B s ⊤ := by rw [hW, B_eq, top_inf_eq]
  subst hW'
  obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_map_of_isCompact M s ⊤ isCompact_univ y
  exact ⟨n, t, ht⟩

/-- The qcqs lemma (uniqueness) for `V = ⊤`. -/
theorem exists_pow_smul_eq_zero_top [CompactSpace X] {W : X.Opens}
    (hW : W = X.basicOpen s) (t : Γ(M, ⊤)) (ht : M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t = 0) :
    ∃ n : ℕ, s ^ n • t = 0 := by
  have hW' : W = B s ⊤ := by rw [hW, B_eq, top_inf_eq]
  subst hW'
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isCompact M s ⊤ isCompact_univ t ht
  rw [rs_top] at hn
  exact ⟨n, hn⟩

end AlgebraicGeometry.Scheme.Modules.Stacks01lcAux

namespace AlgebraicGeometry.Scheme.Modules.Stacks01lcAux

open AlgebraicGeometry

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (g : X ⟶ Spec R) (M : X.Modules)

/-- The `R`-action on sections of `g_*M` over `V ⊆ Spec R` is the action of `g^♯((ΓSpecIso R)⁻¹ r)`
restricted to `g⁻¹V`. -/
theorem smul_pushforward_spec (V : (Spec R).Opens) (r : R) (x : Γ(M, g ⁻¹ᵁ V)) :
    (r • (show Γ((pushforward g).obj M, V) from x) : Γ((pushforward g).obj M, V)) =
      (X.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ V ≤ ⊤)).op (g.appTop ((Scheme.ΓSpecIso R).inv r)) • x :
        Γ(M, g ⁻¹ᵁ V)) := by
  rw [smul_Spec_def]
  change ((g.app V ((Spec R).presheaf.map V.leTop.op ((Scheme.ΓSpecIso R).inv r))) • x :
    Γ(M, g ⁻¹ᵁ V)) = _
  congr 1
  have h1 := ConcreteCategory.congr_hom (g.naturality V.leTop.op) ((Scheme.ΓSpecIso R).inv r)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  rw [h1]
  rfl

/-- Stacks 01LC over an affine base `Spec R`: `X` quasi-compact quasi-separated, `M` quasi-coherent,
then `g_*M` is quasi-coherent (via `IsLocalizing` and the qcqs lemma for modules). -/
theorem isQuasicoherent_pushforward_spec [CompactSpace X] [QuasiSeparatedSpace X]
    [M.IsQuasicoherent] : ((pushforward g).obj M).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing]
  intro r
  obtain ⟨s, hs⟩ : ∃ s : Γ(X, ⊤), s = g.appTop ((Scheme.ΓSpecIso R).inv r) := ⟨_, rfl⟩
  have hW : g ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec R).Opens) = X.basicOpen s := by
    rw [hs, ← basicOpen_eq_of_affine, preimage_basicOpen_top]
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · exact isUnit_algebraMap_end_of_le_basicOpen r le_rfl
  · intro x
    obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_map_top M s hW
      (x : Γ(M, g ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec R).Opens)))
    refine ⟨n, t, ?_⟩
    change r ^ n • x = M.presheaf.map
      (homOfLE (le_top : g ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ ⊤)).op t
    refine (smul_pushforward_spec g M _ (r ^ n) x).trans ?_
    rw [map_pow, map_pow, ← hs, map_pow]
    exact ht.symm
  · intro t ht
    have ht' : M.presheaf.map
        (homOfLE (le_top : g ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ ⊤)).op t = 0 := ht
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_top M s hW t ht'
    refine ⟨n, ?_⟩
    refine (smul_pushforward_spec g M ⊤ (r ^ n) t).trans ?_
    rw [map_pow, map_pow, ← hs, map_pow]
    have e : X.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ (⊤ : (Spec R).Opens) ≤ ⊤)).op s = s := rs_top s
    rw [e]
    exact hn

/-- Stacks 01LC over an affine base: `X` quasi-compact quasi-separated, `Y` affine. -/
theorem isQuasicoherent_pushforward_of_isAffine_target {Y : Scheme.{u}} [IsAffine Y]
    [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Y) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  have h1 := isQuasicoherent_pushforward_spec (f ≫ Y.isoSpec.hom) M
  have h2 : ((pushforward Y.isoSpec.inv).obj
      ((pushforward (f ≫ Y.isoSpec.hom)).obj M)).IsQuasicoherent :=
    AffineTilde.isQuasicoherent_pushforward_hom Y.isoSpec.symm _
  refine (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso ?_ h2
  exact (pushforwardComp (f ≫ Y.isoSpec.hom) Y.isoSpec.inv).app M ≪≫
    (pushforwardCongr (by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])).app M

end AlgebraicGeometry.Scheme.Modules.Stacks01lcAux

/-- Stacks 01LC: the pushforward of a quasi-coherent module along a quasi-compact quasi-separated morphism
is quasi-coherent. Proof: see the file header (qcqs lemma for modules + `IsLocalizing` on affine opens of
the target). -/
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  refine AffinePushforwardAux.isQuasicoherent_of_affineOpens_restrict _ fun V => ?_
  have : IsAffine V.1 := V.2
  have hc : CompactSpace (f ⁻¹ᵁ V.1) :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage V.2.isCompact)
  have hqs : QuasiSeparatedSpace (f ⁻¹ᵁ V.1) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ V.1).2).mp
      (f.isQuasiSeparated_preimage V.2.isQuasiSeparated)
  have := Stacks01lcAux.isQuasicoherent_pushforward_of_isAffine_target
    (M.restrict (f ⁻¹ᵁ V.1).ι) (f.resLE V.1 (f ⁻¹ᵁ V.1) le_rfl)
  exact (SheafOfModules.isQuasicoherent V.1.toScheme.ringCatSheaf).prop_of_iso
    (AffinePushforwardAux.pushforwardRestrictIso f M V.1).symm this

end
