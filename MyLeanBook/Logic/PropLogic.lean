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


-- TODO: 3.1.4否定から再開
