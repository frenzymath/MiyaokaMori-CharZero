import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ExtensionLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAdditiveShortExact
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.SaturatedLineSubsheaf
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.SubbundleFiltrationExtendByLine

/-! # Filtration of a vector bundle on a curve with line bundle quotients

Every vector bundle on a curve has a filtration by subbundles with line bundle quotients `Q_i`
(repeatedly saturate a rational line and iterate on the quotient).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem exists_subbundleFiltration {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (E : AlgebraicGeometry.VectorBundle C.toVariety) :
    Nonempty (SubbundleFiltration E E.rank) := by
  have hmain : ∀ (n : ℕ) (E : AlgebraicGeometry.VectorBundle C.toVariety),
      E.rank = n → Nonempty (SubbundleFiltration E n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E hE
      by_cases hn : n = 0
      · have hE0 : E.rank = 0 := by simpa [hn] using hE
        have hF : Nonempty (SubbundleFiltration E 0) := by
          refine ⟨{
            sub := fun _ => E
            incl := fun i => Fin.elim0 i
            mono := fun i => Fin.elim0 i
            rank_eq := fun i => by simpa [hE0]
            lastIso := Iso.refl _
            lineQuotient := fun i => Fin.elim0 i
            quotient_iso := fun i => Fin.elim0 i }⟩
        simpa [hn] using hF
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        have hEpos : 0 < E.rank := by simpa [hE] using hpos
        obtain ⟨L, i, hi, hqLF⟩ := exists_line_subbundle E hEpos
        letI : Mono i := hi
        let Qmod := CategoryTheory.Limits.cokernel i
        letI : Epi (CategoryTheory.Limits.cokernel.π i) := by
          infer_instance
        letI : E.toModules.IsFiniteType := E.isFiniteType
        have hqFT : Qmod.IsFiniteType := by
          refine AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi_free_pullback Qmod
            (fun x => ?_)
          obtain ⟨U, J, hJ, π, hx, hπ⟩ :=
            AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType
              E.toModules x
          refine ⟨U, J, hJ,
            π ≫ (AlgebraicGeometry.Scheme.Modules.pullback U.ι).map
              (CategoryTheory.Limits.cokernel.π i),
            hx, ?_⟩
          have hmap :
              Epi ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).map
                (CategoryTheory.Limits.cokernel.π i)) :=
            (AlgebraicGeometry.Scheme.Modules.pullback U.ι).map_epi _
          exact @epi_comp _ _ _ _ _ _ hπ _ hmap
        let S : CategoryTheory.ShortComplex C.toScheme.Modules :=
          CategoryTheory.ShortComplex.mk i (CategoryTheory.Limits.cokernel.π i)
            (CategoryTheory.Limits.cokernel.condition i)
        have hS : S.ShortExact := by
          refine { exact := CategoryTheory.ShortComplex.exact_cokernel i }
        have hqRank : ∀ x : C.toScheme,
            AlgebraicGeometry.Scheme.Modules.rankAtStalk Qmod x = E.rank - 1 := by
          intro x
          have hadd := AlgebraicGeometry.Scheme.Modules.rankAtStalk_add_of_shortExact hS x
          have hL : AlgebraicGeometry.Scheme.Modules.rankAtStalk L.toModules x = 1 := by
            rw [L.rankAtStalk_eq x, L.rank_eq_one]
          have hERank : AlgebraicGeometry.Scheme.Modules.rankAtStalk E.toModules x = E.rank :=
            E.rankAtStalk_eq x
          have hadd' :
              AlgebraicGeometry.Scheme.Modules.rankAtStalk L.toModules x +
                AlgebraicGeometry.Scheme.Modules.rankAtStalk Qmod x =
                AlgebraicGeometry.Scheme.Modules.rankAtStalk E.toModules x := by
            simpa [S, Qmod] using hadd.symm
          omega
        let Q : AlgebraicGeometry.VectorBundle C.toVariety := {
          toModules := Qmod
          rank := E.rank - 1
          locallyFree := hqLF
          isFiniteType := hqFT
          rankAtStalk_eq := hqRank }
        have hQr : Q.rank < n := by
          dsimp [Q]
          omega
        obtain ⟨F⟩ := ih Q.rank hQr Q (by rfl)
        have hresult := SubbundleFiltration.extendByLine E Q L i (Iso.refl _) (by
          dsimp [Q]
          omega) F
        simpa [hE] using hresult
  exact hmain E.rank E rfl

end
