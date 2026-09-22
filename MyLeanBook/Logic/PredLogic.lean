/-- （Leanの標準の）自然数上の述語 -/
def P (n : Nat) : Prop := n = n

example : ∀ a : Nat, P a := by
  -- x : Natが任意に与えられたとする
  intro x

  -- Pを展開すれば明らか
  dsimp [P]

/-- すべての自然数xについてP xが成り立つなら、P 0も成り立つ-/
example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  -- hを0に適用すれば明らか
  exact h 0

/-- 偶数であることを表す述語 -/
def even (n : Nat) : Prop := ∃ m : Nat, n = m + m

/-- 4 : Natは偶数 -/
example : even 4 := by
  exists 2

example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x) : ∃ x : α, Q x := by
  -- 仮定hが存在を主張しているyを取り出す
  obtain ⟨y, hy⟩ := h

  -- このyが求めるものである
  exists y

  -- なぜなら、P y ∧ Q y が成り立つから
  exact hy.right

/-
# ∀ と ∃ の対比

どちらも正体は関数まわりの話で、作る側と使う側がきれいに裏返しになっている。

## ∀ x, P x （すべての x について）

  作る（ゴールにある）  intro x
      任意の x を1つ受け取り、それについて示す。どんな値でも成り立つと
      示さないといけないので、作るのは大変。

  使う（仮定にある）    h 0
      好きな値を代入するだけ。使うのは楽。

## ∃ x, P x （ある x が存在して）

  作る（ゴールにある）  exists 2
      具体例を1つ出せばよいので、作るのは楽。

  使う（仮定にある）    obtain ⟨m, hm⟩ := h
      中身に名前を付けて取り出す必要があるので、使うのは少し手間。

つまり ∀ は「作るのが大変で使うのが楽」、∃ は「作るのが楽で使うのが手間」。
ちょうど裏返しの関係になっている。

## ∀ の正体は関数

∀ x : Nat, P x は「自然数 x をもらうと P x の証明を返す関数」。
P → Q が「P の証明をもらうと Q の証明を返す関数」だったのと同じ仕組みで、
→ は返り値の型が引数に依存しない特別な場合にすぎない。
だから ∀ にも → にも intro が使えるし、使うときはどちらも関数適用になる。

  h : P → Q           に hp : P を渡すと   h hp : Q      証明を渡す
  h : ∀ x : Nat, P x  に 0 を渡すと        h 0  : P 0    値を渡す

## ∃ は証拠と証明の組

∃ の証明は ⟨証拠, その証拠が条件を満たす証明⟩ という組で表される。

  example : even 4 := ⟨2, rfl⟩        -- 証拠 2 と、4 = 2 + 2 の証明 rfl

exists 2 はこれをタクティクで書いたもの。証拠を出したあと、残りが計算で
片付く場合はそのまま閉じてくれる。分けて書くとこうなる。

  apply Exists.intro 2   -- 証拠を出す。⊢ 4 = 2 + 2 が残る
  rfl                    -- 計算して閉じる
-/

/-- 人間たちの集合 -/
opaque Human : Type
-- opaqueはdefと同様に新しい定数を定義できるが、実装を与えず存在だけ宣言する

/-- 愛の関係 -/
opaque Love : Human → Human → Prop

-- 専用の中間記法を用意する
-- infixはパースの優先順位
@[inherit_doc] infix:50 "-♡→" => Love

/-- すべての人に愛されているアイドルが存在する -/
def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -♡→ idol

/-- 誰にでも好きな人の1人くらいいる -/
def EveryoneLovesSomeone : Prop := ∀ h : Human, ∃ tgt : Human, h -♡→ tgt
-- 上の2つの例は、量化子の順番が異なるだけで意味がガラリと変わる

#check ∃ philan : Human, ∀ h : Human, philan -♡→ h
-- すべての人を愛してる博愛主義者(philanthropist)が存在する
def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -♡→ h

#check ∀ h : Human, ∃ lover : Human, lover -♡→ h
-- どんな人も、誰かには好かれている
def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -♡→ h

/-- 博愛主義者が存在するならば、すべての人は誰かに愛されている -/
example : PhilanExists → EveryoneLoved := by
  -- 博愛主義者の存在を仮定する
  intro h

  -- 存在が主張されている博愛主義者をphilanとする
  -- このとき定義からh: ∀ human : Human, philan -♡→ humanが成り立つ
  obtain ⟨philan, h⟩ := h

  -- このときEveryoneLovedを示したい
  -- 定義より、∀ (h : Human), ∃ lover, lover -♡→ hを示せば良い
  dsimp [EveryoneLoved]

  -- そこで任意にhuman : Humanが与えられたと仮定する
  intro human

  -- ここで∃ lover : Human, lover -♡→ を示したいが、
  -- lover = philanとすればよい
  exists philan

  -- なぜなら、philan -♡→ humanが成り立つからである
  -- これで示すべきことが言えた
  exact h human

-- ∃ が仮定にある  → obtain で中身を取り出す      （philan を手に入れる）
-- ∀ がゴールにある → intro で任意の1人をもらう    （human を受け取る）
-- ∃ がゴールにある → exists で証拠を出す          （philan を差し出す）
-- ∀ が仮定にある  → 値を渡して使う                （h human）

/-- アイドルがいるなら、全員そのアイドルを好きなのだから、誰にでも好きな人はいる -/
example : IdolExists → EveryoneLovesSomeone := by
  dsimp [EveryoneLovesSomeone]
  intro hidol h
  obtain ⟨idol, hidol⟩ := hidol
  exists idol
  exact hidol h

-- ∃∀ → ∀∃ を示す証明は、いつもこの4手になります。
-- 1. intro        仮定の ∃∀ と、ゴールの ∀ を受け取る
-- 2. obtain       仮定の ∃ を分解して、1人を手に入れる
-- 3. exists       その1人を、ゴールの ∃ の証拠として出す
-- 4. exact        仮定の ∀ に値を渡して、残りを埋める
