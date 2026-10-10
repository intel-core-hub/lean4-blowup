import BlowupStrict

/-!
# ブローアップ(層6: 二つのチャートの統合)

`k` を代数閉体、`f ≠ 0` とする。`𝔸² × ℙ¹` における `φ⁻¹(Y ∖ 0) ∩ X` の
**射影的な閉包**(斉次多項式で消える点の共通零点)は、
`X ∩ Z(strictEq f)` に一致する(`strict_eq_projClosure`)。

チャート `t`・`u` ごとの結果(`strictEq_mem_iff_chart_t/u`)と、チャートの被覆
(`chart_cover`)から従う。脱斉次化 `defT`/`defU` で斉次多項式をチャートの 2 変数多項式に移す。
-/

open MvPolynomial Projectivization

namespace Blowup

section closure

variable {k : Type*} [Field k]

/-- `φ⁻¹(Y ∖ 0) ∩ X`。 -/
def preimageX (f : Poly k) : Set ((Fin 2 → k) × Projectivization k (Fin 2 → k)) :=
  {z | z ∈ blowupSet k ∧ z.1 ≠ 0 ∧ eval z.1 f = 0}

/-- `𝔸² × ℙ¹` での射影的な閉包:`S` 上で消える斉次多項式の共通零点。 -/
def projClosure (S : Set ((Fin 2 → k) × Projectivization k (Fin 2 → k))) :
    Set ((Fin 2 → k) × Projectivization k (Fin 2 → k)) :=
  {z | ∀ G : MvPolynomial (Fin 4) k, (∃ d, IsBihom d G) → (∀ w ∈ S, w ∈ projZeroSet G) →
    z ∈ projZeroSet G}

lemma eval_aeval_vec4 (φ : Fin 4 → Poly k) (G : MvPolynomial (Fin 4) k) (p : Fin 2 → k) :
    eval p (aeval φ G) = eval (fun i => eval p (φ i)) G := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a i ha => simp only [map_mul, ha, aeval_X, eval_X]

/-- チャート `t` への脱斉次化 `G ↦ G(x, x u, 1, u)`(座標 `(x, u) = (X 0, X 1)`)。 -/
noncomputable def defT (G : MvPolynomial (Fin 4) k) : Poly k :=
  aeval (![X 0, X 0 * X 1, 1, X 1] : Fin 4 → Poly k) G

/-- チャート `u` への脱斉次化 `G ↦ G(t y, y, t, 1)`(座標 `(t, y) = (X 0, X 1)`)。 -/
noncomputable def defU (G : MvPolynomial (Fin 4) k) : Poly k :=
  aeval (![X 0 * X 1, X 1, X 0, 1] : Fin 4 → Poly k) G

lemma eval_defT (G : MvPolynomial (Fin 4) k) (p P v : Fin 2 → k) (hP0 : P 0 = p 0)
    (hP1 : P 1 = p 0 * p 1) (hv0 : v 0 = 1) (hv1 : v 1 = p 1) :
    eval p (defT G) = evalPair P v G := by
  have hfun : (fun i : Fin 4 => eval p ((![X 0, X 0 * X 1, 1, X 1] : Fin 4 → Poly k) i)) =
      ![P 0, P 1, v 0, v 1] := by
    funext i
    fin_cases i <;> simp [hP0, hP1, hv0, hv1]
  rw [defT, eval_aeval_vec4, hfun] <;> rfl

lemma eval_defU (G : MvPolynomial (Fin 4) k) (p P v : Fin 2 → k) (hP0 : P 0 = p 0 * p 1)
    (hP1 : P 1 = p 1) (hv0 : v 0 = p 0) (hv1 : v 1 = 1) :
    eval p (defU G) = evalPair P v G := by
  have hfun : (fun i : Fin 4 => eval p ((![X 0 * X 1, X 1, X 0, 1] : Fin 4 → Poly k) i)) =
      ![P 0, P 1, v 0, v 1] := by
    funext i
    fin_cases i <;> simp [hP0, hP1, hv0, hv1]
  rw [defU, eval_aeval_vec4, hfun] <;> rfl

lemma chart_t_rel {P : Fin 2 → k} {u : k}
    (hz : (P, mk k ![1, u] (one_ne_zero_vec u)) ∈ blowupSet k) : P 1 = P 0 * u := by
  rw [mem_blowupSet_iff (one_ne_zero_vec u) rfl] at hz
  simpa using hz.symm

lemma chart_u_rel {P : Fin 2 → k} {t : k}
    (hz : (P, mk k ![t, 1] (one_ne_zero_vec' t)) ∈ blowupSet k) : P 0 = t * P 1 := by
  rw [mem_blowupSet_iff (one_ne_zero_vec' t) rfl] at hz
  simpa using hz

variable [IsAlgClosed k]

/-- **二つのチャートの統合**:`φ⁻¹(Y ∖ 0) ∩ X` の射影的な閉包は `X ∩ Z(strictEq f)`。 -/
theorem strict_eq_projClosure {f : Poly k} (hf : f ≠ 0) :
    blowupSet k ∩ projZeroSet (strictEq f) = projClosure (preimageX f) := by
  ext ⟨P, L⟩
  constructor
  · rintro ⟨hzX, hzS⟩ G ⟨d, hG⟩ hvan
    rcases chart_cover L with ⟨u, rfl⟩ | ⟨t, rfl⟩
    · have h1 := chart_t_rel hzX
      have hcl := (strictEq_mem_iff_chart_t hf hzX).mp hzS
      have hvanT : ∀ s ∈ preimageT f, eval s (defT G) = 0 := by
        rintro s ⟨hs0, hs1⟩
        have hne : (![s 0, s 0 * s 1] : Fin 2 → k) ≠ 0 := fun h0 => hs0 (by simpa using congrFun h0 0)
        have hw : (![s 0, s 0 * s 1], mk k ![1, s 1] (one_ne_zero_vec (s 1))) ∈ preimageX f :=
          ⟨chart_mem (s 0) (s 1), hne, hs1⟩
        have := (mem_projZeroSet_iff hG (one_ne_zero_vec (s 1)) rfl).mp (hvan _ hw)
        rw [eval_defT G s ![s 0, s 0 * s 1] ![1, s 1] rfl rfl rfl rfl]
        exact this
      have hg := hcl (defT G) hvanT
      rw [mem_projZeroSet_iff hG (one_ne_zero_vec u) rfl,
        ← eval_defT G ![P 0, u] P ![1, u] rfl h1 rfl rfl]
      exact hg
    · have h0 := chart_u_rel hzX
      have hcl := (strictEq_mem_iff_chart_u hf hzX).mp hzS
      have hvanU : ∀ s ∈ preimageU f, eval s (defU G) = 0 := by
        rintro s ⟨hs1, hs2⟩
        have hne : (![s 0 * s 1, s 1] : Fin 2 → k) ≠ 0 := fun h0 => hs1 (by simpa using congrFun h0 1)
        have hw : (![s 0 * s 1, s 1], mk k ![s 0, 1] (one_ne_zero_vec' (s 0))) ∈ preimageX f :=
          ⟨chart_mem' (s 0) (s 1), hne, hs2⟩
        have := (mem_projZeroSet_iff hG (one_ne_zero_vec' (s 0)) rfl).mp (hvan _ hw)
        rw [eval_defU G s ![s 0 * s 1, s 1] ![s 0, 1] rfl rfl rfl rfl]
        exact this
      have hg := hcl (defU G) hvanU
      rw [mem_projZeroSet_iff hG (one_ne_zero_vec' t) rfl,
        ← eval_defU G ![t, P 1] P ![t, 1] h0 rfl rfl rfl]
      exact hg
  · intro h
    have hX : (P, L) ∈ blowupSet k := by
      have := h (blowEq k) ⟨1, isBihom_blowEq⟩ (fun w hw => by
        rw [← blowupSet_eq_projZeroSet]; exact hw.1)
      rwa [← blowupSet_eq_projZeroSet] at this
    refine ⟨hX, h (strictEq f) ⟨_, isBihom_strictEq f⟩ ?_⟩
    rintro ⟨Q, M⟩ ⟨hwX, hw0, hwf⟩
    change Q ≠ 0 at hw0
    change eval Q f = 0 at hwf
    rcases chart_cover M with ⟨u, rfl⟩ | ⟨t, rfl⟩
    · have h1 := chart_t_rel hwX
      have hQ0 : Q 0 ≠ 0 := fun h0 => hw0 (by ext i; fin_cases i <;> simp [h0, h1])
      have e : (![Q 0, Q 0 * u] : Fin 2 → k) = Q := by
        rw [← h1]; exact (vec2_eta Q).symm
      rw [strictEq_mem_iff_chart_t hf hwX]
      intro g hg
      exact hg _ ⟨hQ0, by change eval ![Q 0, Q 0 * u] f = 0; rw [e]; exact hwf⟩
    · have h0 := chart_u_rel hwX
      have hQ1 : Q 1 ≠ 0 := fun h1 => hw0 (by ext i; fin_cases i <;> simp [h0, h1])
      have e : (![t * Q 1, Q 1] : Fin 2 → k) = Q := by
        rw [← h0]; exact (vec2_eta Q).symm
      rw [strictEq_mem_iff_chart_u hf hwX]
      intro g hg
      exact hg _ ⟨hQ1, by change eval ![t * Q 1, Q 1] f = 0; rw [e]; exact hwf⟩

end closure

end Blowup
