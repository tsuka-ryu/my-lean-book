/-- 3重否定の簡略化 -/
example (P : Prop) : ¬¬¬ P → ¬ P := by
  -- ¬¬¬ PかつPと仮定する
  intro hn3p hp

  -- ここで¬¬ Pが成り立つ
  have hn2p : ¬¬ P := by
    -- なぜなら、¬ Pであると仮定した時
    intro hnp
    -- 仮定のPと矛盾するから
    contradiction

  -- これで ¬¬¬ Pと¬¬ Pが得られたがこれは矛盾である
  contradiction

-- 証明の名前を省略するとthisになる
example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp

  have : ¬¬ P := by
    intro hnp
    contradiction

  -- this : ¬¬ Pという仮定が得られる
  guard_hyp this : ¬¬ P

  contradiction

/-
# 排中律について

`P ∨ ¬ P` を排中律という。「どんな命題も、成り立つか成り立たないかのどちらかであり、
中間はない」という主張。「排中」は「中間を排除する」の意味。

## Lean ではそのまま証明できない

`A ∨ B` を示すには `left` か `right` で「どちら側か」を宣言し、その側の証拠を出す
必要がある。しかし P は中身の分からない任意の命題なので、どちら側かは一般には
決められない。だから排中律は証明できない。こういう立場を構成的（直観主義的）論理と呼ぶ。

## 使いたければ公理として認める

Lean には公理として用意されている。

  #check @Classical.em   -- ∀ (p : Prop), p ∨ ¬p

これは「証明した」のではなく「認めることにした」もの。
Lean が最初から認めている公理は実質3つだけ。

  propext           同値な命題は等しい  (a ↔ b) → a = b
  Quot.sound        商型（同値なものの同一視）の健全性
  Classical.choice  選択公理。排中律はここから導かれる

ほかに sorryAx（sorry の正体）と Lean.ofReduceBool / ofReduceNat
（native_decide 用。コンパイラとランタイムまで信頼することになる）がある。

依存する公理は `#print axioms 名前` で調べられる。結果に sorryAx が出たら
証明に穴が残っている、という検査にも使える。

## それでも二重否定なら証明できる

  P ∨ ¬ P        どちら側か示せないので証明できない
  ¬ (P ∨ ¬ P)    これは誤り。証明できない
  ¬¬ (P ∨ ¬ P)   公理なしで証明できる ← 下の example

構成的論理は排中律を「否定している」のではなく「主張しない」だけ。
だから「排中律は偽だ」と主張する立場は破綻する。それがこの二重否定の中身。

下の example に名前を付けて `#print axioms` すると
"does not depend on any axioms" と表示される。

## どこで踏みとどまっているのか

  ¬¬ (P ∨ ¬ P)
      ↓ 二重否定除去 ¬¬A → A （構成的には認められない）
    P ∨ ¬ P

二重否定除去と排中律は同じ強さを持つ。古典論理はこの一歩を認める立場、
構成的論理は認めない立場、という違いになる。

たとえ話。箱の中身が赤かどうか。

  「赤か赤以外か、どちらでもない」と言う      → 矛盾する
  「赤である」「赤以外である」と言い切る      → 箱を開けないと言えない
  「どちらかではあるはずだが、まだ言えない」  → 構成的な立場

¬¬ (P ∨ ¬ P) は1つ目を否定しているだけで、箱は開けていない。

## Glivenko の定理 (1929)

命題論理の式 A について、

  A が古典論理で証明できる  ⟺  ¬¬A が構成的論理で証明できる

古典論理で示せることは二重否定を被せれば構成的にも示せる。ただし最後に
その二重否定を外す一歩だけは渡れない。この example はその代表例。
-/

/-- 排中律の二重否定 -/
example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  -- ¬ (P ∨ ¬ P)と仮定する
  intro h

  -- have と suffices は向きが逆
  --
  --   have h : X := 証明        先に X を証明する。仮定が増え、ゴールはそのまま
  --   suffices h : X from 証明  X があれば済むことを示す。ゴールが X に差し替わる
  --
  -- have は「材料を作ってから進む」、suffices は「ゴールをもっと簡単な形に取り替える」。
  -- 答案で言えば「X を示せば十分である。なぜなら…。以下、X を示す」という構成にあたる。

  -- ここで、¬ Pを示せば十分である
  suffices hyp : ¬ P from by
    -- なぜなら、¬ Pが成り立つなら特に P ∨ ¬ Pが成り立つので
    have : P ∨ ¬ P := by
      right
      exact hyp

    -- 最初の仮定と矛盾するから
    contradiction

  -- 無事ゴールを ¬ P に帰着できた

  -- 以下、¬ P を示す
  guard_target =ₛ ¬ P

  -- P であると仮定する
  intro hq

  -- このときP ∨ ¬ P が成り立つ
  have : P ∨ ¬ P := by
    left
    exact hq

  -- これは矛盾
  contradiction

example (P : Prop) : (P → True) ↔ True := by
  exact?

example (P : Prop) : (True → P) ↔ P := by
  exact?

example (P Q : Prop) (h : ¬P ↔ Q) : (P → False) ↔ Q := by
  rw [show (P → False) ↔ ¬ P from by rfl]
  rw [h]

example : P → P := by
  intro hp
  exact hp

/--
  P ↔ ¬P（P と ¬P が同値）になることはありえない、を示す
  「この文は偽である」という嘘つきのパラドクスをLeanでは作れないらしい
  「この文は偽である」を形にすると、自分自身の否定と同値な命題 L ↔ ¬L になります。これを作るには、L の定義の中で L を使わなければいけません。
  Lean では、これは再帰的な定義として扱われます。そして Lean は再帰定義に対して「必ず有限回で止まること」の証明を要求します。
  L には引数がなく、呼び出すたびに減っていくものが何もありません。¬L を展開すると ¬¬L、さらに ¬¬¬L… と無限に続き、決して止まりません。だから停止性を示せず、定義そのものが却下されます。
  Lean の定義は「すでに存在するものだけを使って組み立てる」という積み上げ式なので、自分自身を含む命題は、そもそも書く手段がありません。
 -/
example (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h

  have hnp : ¬ P := by
    intro hq
    have : ¬ P := by
      rw [h] at hq
      exact hq
    contradiction

  have hp : P := by
    rw [← h] at hnp
    exact hnp
  contradiction

-- 1. P だとすると → 同値性から ¬P になる → 矛盾 → よって ¬P      （前半）
-- 2. ¬P が言えた → 同値性から P も言える                        （後半）
-- 3. P と ¬P がそろった → 矛盾                                  （最後）
