#check Prop

-- これは命題
#check (1+1=3:Prop)

-- これは命題ではなく、命題への関数
#check (fun n => n + 3 = 39 : Nat → Prop)

#check True

#check False

/-- Trueはなにも主張していないので、何もなくても示せる -/
example : True := by trivial

/-- 「Pが成り立っている」という仮定で証明する -/
example (P : Prop) (h : P) : P := by
  exact h

-- Leanは証明も値として扱える（！）
-- (h : P)は「hという箱の中に、Pの証明が入っている」と読む

/-- ゴールを直接証明できる仮定を自動的に適用することでゴールを閉じる-/
example (P : Prop) (h : P) : P := by
  assumption

/--
  逆に矛盾からは何でも示せるため、仮定にFalseがあれば何でも示せる
  フェルマーの大定理
-/
example (h : False) : ∀ x y z n : Nat,
    n ≥ 3 → x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
  trivial

/-- 「含意（→）= 命題PとQに対して、PならばQが成り立つ」は右結合 -/
example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

#eval True → True
#eval True → False
#eval False → True
#eval False → False

/-- いわゆるモーダスポネンス（三段論法）-/
example (P Q : Prop) (h : P → Q) (hp : P) : Q :=by
  -- P → Qが成り立つので、Qを示すにはPを示せば良い
  apply h

  -- Pの成立はわかっているので、証明終わり
  apply hp

/-- 関数適用っぽく h hpともかける-/
example (P Q : Prop) (h : P → Q) (hp : P) : Q :=by
  exact h hp

-- exact … これで完全に埋まるものを出す。埋まらなければエラー
-- apply … 結論部分だけ合っていればよい。足りない前提は新しいゴールとして残る

/-- 含意の導入。Qであることがわかっているなら、仮定を足しても正しい -/
example (P Q : Prop) (hq : Q) : P → Q := by
  -- P → Qを示したいのでPであると仮定する
  intro hp

  -- あとはQを示せば良いが、これは仮定されていた
  exact hq

-- ゴール        ⊢ P → Q
--                 ↑   ↑
--                 │   └─ ここが新しいゴールになる
--                 └───── ここが新しい仮定の型になる

-- 自分が書いた名前  intro hp
--                       ↓
-- 結果            hp : P  という仮定ができる


#eval ¬ True
#eval ¬ False

/-- Pと仮定すると矛盾する、ということは¬ Pと等しい -/
example (P : Prop) : (¬ P) = (P → False) := by
  rfl
-- ¬ Pは含意（→）の特別な場合

/-- Pと¬ Pを同時に仮定すると矛盾する -/
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  -- ¬ P は P → Falseに等しいので、Pを示せば良い
  apply hnp

  -- 仮定hp : Pがあるので、証明終わり
  exact hp

/-- 対偶が元の命題と同値になることの、片方のケース -/
example (P Q : Prop) (h : P → ¬ Q) : Q → ¬ P := by
  -- Qならば ¬ P を示したいのでQであったと仮定する
  intro hq

  -- ¬ PはP → Falseに等しいので、
  -- さらにPであったと仮定する
  intro hp

  -- 仮定h : P → Q → Falseに適用してFalseが得られる
  exact h hp hq

-- 仮定にPと¬ Pが両方あるときは、明らかに矛盾
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  contradiction

-- 矛盾からは何でも示せる、無関係な命題Q、爆発律
example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  -- 矛盾を示せば良い
  exfalso

  -- 仮定に矛盾があるので💡終わり
  contradiction

-- 同値
#eval True ↔ True
#eval True ↔ False
#eval False ↔ True
#eval False ↔ False

-- constructorタクティクスで同値性を示す
example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  -- 両方を示すことで証明する
  constructor

  -- まず左から右を示す
  case mp =>
    intro h
    exact h hq

  -- 右から左を示す
  case mpr =>
    intro hp hq
    exact hp

-- rwタクティクで同値性を使う
example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- P ↔ Qが仮定にあるので、Pの代わりにQを示せば良い
  rw [h]

  -- 仮定hp: Qがあるので、照明終わり
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [←h]
  exact hp

-- 3.1.6 論理積 and
#eval True ∧ True
#eval True ∧ False
#eval False ∧ True
#eval False ∧ False

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h: P ∧ Q) : Q := by
  exact h.right

-- 3.1.7 論理和 or
#eval True ∨ True
#eval True ∨ False
#eval False ∨ True
#eval False ∨ False

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  case inl hp =>
    right
    exact hp
  case inr hq =>
    left
    exact hq

example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  -- ¬ P ∨ Q と Pを仮定する、 ⊢ Qが残る
  intro h hp
  -- ¬ P ∨ Qのどちらかは成り立つという仮定
  cases h with
  -- 左辺の¬ Pをhnpとするが、すでにhp : Pがあるから矛盾（？）
  | inl hnp => contradiction
  -- 右辺の Qはexactするだけ
  | inr hq => exact hq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  -- 同値 ↔ をconstructorで → と ← に割る
  constructor <;> intro h1
  -- mpの分岐
  -- constructorで ¬P ∧ ¬Qを割る、∧ は両方を示す必要がある
  · constructor <;> intro h2
    -- mp.l、⊢Falseなので矛盾を作りたい
    · apply h1 -- h1は P ∨ Qを受け取ると Falseを返す、なぜなら ¬ なので、⊢ P ∨ Qになった
      left
      assumption -- exact h2でも同じ
    -- mp.r、⊢Falseなので矛盾を作りたい
    · apply h1
      right
      assumption
  -- mprの分岐、h1 → ¬ (P ∨ Q)を示す
  -- ¬ (P ∨ Q)は (P ∨ Q) → Falseと読み替える、矢印があるからintroできる
  · intro hpq -- P ∨ Q を仮定するので ⊢ Falseになった、ので矛盾を作ればよい
    cases hpq with -- P ∨ Qを示す
    | inl hp =>
      apply h1.left -- ¬P は P → FalseなのでゴールがPになる
      assumption -- exact hpと同じ
    |inr hq =>
      apply h1.right
      assumption

-- TODO: 3.2から
