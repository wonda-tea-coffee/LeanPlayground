/-
# 素数の無限性の証明 (Proof of Infinitude of Primes)

Mathlibを使わず、Lean 4 の標準ライブラリのみで
素数が無限に存在することをユークリッドの方法で証明する。

## 証明の方針（ユークリッドの証明）
任意の自然数 n に対して n より大きい素数が存在することを示す。
N = n! + 1 を考えると N ≥ 2 なので素因数 p が存在する。
もし p ≤ n なら p | n! なので p | (N - n!) = 1 となり矛盾。
よって p > n。
-/

/-! ## Part 1: 素数の定義 -/

/-- 素数の定義: p ≥ 2 かつ p の約数は 1 と p のみ -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- 素数は 2 以上 -/
theorem IsPrime.two_le {p : Nat} (hp : IsPrime p) : 2 ≤ p := hp.1

/-- 素数は正 -/
theorem IsPrime.pos {p : Nat} (hp : IsPrime p) : 0 < p := by
  have := hp.two_le; omega

/-- 2 は素数 -/
theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, fun d hd => ?_⟩
  have h_le := Nat.le_of_dvd (by omega) hd
  have h_pos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
  omega

/-! ## Part 2: 素因数の存在 -/

/-- **素因数の存在**：2 以上の自然数は必ず素因数を持つ。
    強帰納法で証明する。n が素数ならそれ自身、
    合成数なら真の約数の素因数が n の素因数でもある。-/
theorem exists_prime_factor (n : Nat) (hn : 2 ≤ n) : ∃ p, IsPrime p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    -- n 自身が素数か合成数かで場合分け
    rcases Classical.em (∀ d : Nat, d ∣ n → d = 1 ∨ d = n) with h | h
    · -- n は素数: n 自身が素因数
      exact ⟨n, ⟨hn, h⟩, Nat.dvd_refl n⟩
    · -- n は合成数: 1 でも n でもない約数 d が存在
      have ⟨d, hd_dvd, hd_not⟩ : ∃ d, d ∣ n ∧ ¬(d = 1 ∨ d = n) := by
        rcases Classical.em (∃ d, d ∣ n ∧ ¬(d = 1 ∨ d = n)) with h2 | h2
        · exact h2
        · exact absurd (fun d hd => (Classical.em (d = 1 ∨ d = n)).elim id
            (fun h3 => absurd ⟨d, hd, h3⟩ h2)) h
      have hd_ne1 : d ≠ 1 := fun h => hd_not (Or.inl h)
      have hd_nen : d ≠ n := fun h => hd_not (Or.inr h)
      have hd_le := Nat.le_of_dvd (by omega) hd_dvd
      -- d は n の真の約数: 2 ≤ d < n
      have hd_lt : d < n := by omega
      have hd_ge2 : 2 ≤ d := by
        have := Nat.pos_of_dvd_of_pos hd_dvd (by omega : 0 < n); omega
      -- 帰納法の仮定: d の素因数 p が存在する
      obtain ⟨p, hp, hp_dvd_d⟩ := ih d hd_lt hd_ge2
      -- p | d かつ d | n より p | n
      exact ⟨p, hp, Nat.dvd_trans hp_dvd_d hd_dvd⟩

/-! ## Part 3: 階乗 -/

/-- 階乗の定義 -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- 階乗は常に正 -/
theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial]; omega

/-- **階乗の整除性**: 1 ≤ k ≤ n ならば k | n!。
    k は 1, 2, ..., n のいずれかの因子なので n! を割り切る。-/
theorem dvd_factorial {k n : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) : k ∣ factorial n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp [factorial]
    rcases Nat.eq_or_lt_of_le hkn with h | h
    · -- k = n + 1 のとき: k | k * n!
      rw [h]; exact Nat.dvd_mul_right (n + 1) (factorial n)
    · -- k < n + 1、すなわち k ≤ n のとき: IH より k | n!、よって k | (n+1) * n!
      exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_left (factorial n) (n + 1))

/-! ## Part 4: 主定理 -/

/-- **素数の無限性（ユークリッドの定理）**：
    任意の自然数 n に対して、n より大きい素数 p が存在する。

    証明: N = n! + 1 とおく。N ≥ 2 なので素因数 p が存在する。
    もし p ≤ n なら p | n! だが、p | (n! + 1) でもあるので
    p | ((n! + 1) - n!) = 1 となり p = 1。これは p ≥ 2 に矛盾。
    よって p > n。-/
theorem infinite_primes (n : Nat) : ∃ p, p > n ∧ IsPrime p := by
  -- N = n! + 1 ≥ 2
  have hN : 2 ≤ factorial n + 1 := by have := factorial_pos n; omega
  -- N の素因数 p を取る
  obtain ⟨p, hp, hp_dvd⟩ := exists_prime_factor (factorial n + 1) hN
  refine ⟨p, ?_, hp⟩
  -- p > n を示す
  rcases Classical.em (n < p) with h | h
  · exact h
  · -- p ≤ n と仮定して矛盾を導く
    exfalso
    have hpn : p ≤ n := by omega
    -- p | n! (1 ≤ p ≤ n なので)
    have hp_fac : p ∣ factorial n := dvd_factorial (by have := hp.two_le; omega) hpn
    -- p | (n! + 1) かつ p | n! なので p | (n! + 1 - n!) = 1
    have hsub := Nat.dvd_sub hp_dvd hp_fac
    have heq : factorial n + 1 - factorial n = 1 := by omega
    rw [heq] at hsub
    -- p = 1 だが p ≥ 2 で矛盾
    have := Nat.eq_one_of_dvd_one hsub
    have := hp.two_le
    omega
