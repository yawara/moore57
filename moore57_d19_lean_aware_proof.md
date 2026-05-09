# Moore57 における $D_{19}$ 作用排除の Lean 指向自然言語証明

## 0. 目的と現在の形式化境界

本稿の目的は、仮想的な Moore graph $\Gamma$ of degree $57$ and diameter $2$ に、

$$
D_{19}=\langle r,t\mid r^{19}=t^2=1,\ trt=r^{-1}\rangle
$$

が自己同型群として作用する、あるいは部分群として作用する、という仮定から矛盾を導くことである。

Lean 形式化上の目標は、現在 `D19FinalInputs` や `D19GeometricInputs` で入力として残っている次のデータを、実際の $D_{19}$ 作用から構成することである。

1. $56$ 個の selected orbit base。
2. selected orbit base が与える $B,C$ 側の adjacent-moved decomposition。
3. residual split、すなわち選ばれた $B,C$ 側 orbit の補集合が、零寄与部分と $A$-fiber 部分に分かれること。
4. 非自明回転 $r^d$ に対する fixed/`A`-side contribution が常に $38$ であること。
5. trace/character 側から、各非零 $d$ に対して $B,C$ 側から少なくとも $8$ 個の orbit が寄与しなければならないこと。

この文書では、これらを Lean で補題化しやすい順序で記述する。

証明の正しさについて再検討した結果、前回の高次整合性証明の核は維持できる。ただし、Lean 形式化で重要なのは、次の二点を曖昧にしないことである。

- 「residual」と呼ぶ集合には、$u$ や枝集合 $N(u)$ も含めるかどうかを明示する必要がある。本稿では、selected $B,C$ leaf orbit の補集合をまず residual とし、それを

  $$
  \text{zeroPart}=\{u\}\cup N(u),
  \qquad
  \text{aPart}=\bigsqcup_{i\in\mathbb Z/19}L_{a_i}
  $$

  に分ける。
- $A$-fiber contribution $38$ は、「固定された頂点 $(i,p)$ に対して可能な $d$ が少ない」という横方向評価からではなく、固定された非零 $d$ に対して全 $A$-fiber を縦方向に数えることで得る。

---

## 1. 外部既知事実と Moore graph 基本性質

### 既知事実 1.1：Moore57 の SRG パラメータ

$\Gamma$ は、存在すれば強正則グラフ

$$
(v,k,\lambda,\mu)=(3250,57,0,1)
$$

である。従って、任意の隣接二頂点は共通近傍を持たず、任意の非隣接二頂点は一意の共通近傍を持つ。

隣接行列を $A$ とすると、

$$
A^2=56I-A+J,
$$

かつスペクトルは

$$
57^1,
\qquad
7^{1729},
\qquad
(-8)^{1520}
$$

である。

### 既知事実 1.2：可能次数

Diameter $2$ の Moore graph の次数は $2,3,7,57$ に限られる。従って、次数 $19$ または $38$ の Moore graph は存在しない。

### 既知事実 1.3：involution の固定点集合

$\Gamma$ の自己同型 $s$ が involution なら、

$$
\operatorname{Fix}(s)
$$

は $56$ 頂点からなる star、すなわち $K_{1,55}$ である。

この事実は外部入力として扱う。Lean では、少なくとも当面は次の形で仮定として切り出すのがよい。

```lean
InvolutionFixedStar Γ s
```

または、より直接に

```lean
∃ c : V, ∃ leaves : Finset V,
  leaves.card = 55 ∧
  Fix s = insert c leaves ∧
  ... star adjacency conditions ...
```

のような record にする。

### 補題 1.4：三角形禁止

任意の $x,y,z$ について、

$$
x\sim y,\quad y\sim z,\quad z\sim x
$$

は不可能である。

#### 証明

$x\sim y$ なら、$\lambda=0$ より $x,y$ の共通近傍は存在しない。ところが $z$ は $x$ と $y$ の共通近傍になる。矛盾。

### 補題 1.5：$4$-cycle 禁止

相異なる $x_0,x_1,x_2,x_3$ について、

$$
x_0\sim x_1\sim x_2\sim x_3\sim x_0
$$

は不可能である。

#### 証明

対角 $x_0,x_2$ は三角形禁止により非隣接である。しかし $x_1,x_3$ はともに $x_0,x_2$ の共通近傍である。これは $\mu=1$ に反する。

Lean では `IsMoore57.no_four_cycle` 型の補題として使う。

---

## 2. 位数 $19$ の回転の固定点

### 定義 2.1：回転固定部分グラフ

$r$ を位数 $19$ の自己同型とし、

$$
H=\operatorname{Fix}(r)
$$

を $r$ の固定頂点集合で誘導される部分グラフとする。

### 補題 2.2：固定部分グラフ内次数の合同条件

任意の $x\in H$ について、$H$ 内次数 $d_H(x)$ は

$$
d_H(x)\in\{0,19,38,57\}
$$

である。

#### 証明

$r$ は $N(x)$ を置換する。$x$ は固定されているので、この作用の軌道長は $1$ または $19$ である。長さ $1$ の軌道はちょうど $H$ 内の近傍である。従って

$$
57-d_H(x)\equiv0\pmod{19}.
$$

よって $d_H(x)=0,19,38,57$ のいずれかである。

### 補題 2.3：$|H|>1$ なら $H$ は正則である

$|H|>1$ と仮定する。このとき $H$ は正則であり、その次数は $19,38,57$ のいずれかである。

#### 証明

まず、孤立固定点は存在しない。$x,y\in H$ が非隣接なら、$\mu=1$ により一意の共通近傍 $z$ が存在する。$r$ は $x,y$ を固定し、共通近傍の一意性を保存するので、$z$ も $r$ で固定される。従って $z\in H$ である。

非隣接な $x,y\in H$ については、$x,y$ の一意の共通近傍を $z$ とする。$N_H(x)\setminus\{z\}$ の各点 $a$ に対し、$a$ と $y$ は非隣接である。もし $a\sim y$ なら、$x,y$ は $a,z$ という二つの共通近傍を持つからである。従って $a,y$ の一意の共通近傍が存在し、それは $N_H(y)\setminus\{z\}$ に入る。一意性によりこの対応は単射であり、逆向きも同様である。従って

$$
d_H(x)=d_H(y).
$$

隣接する $x,y\in H$ については、補題 2.2 と孤立点不存在から $d_H(x),d_H(y)\ge19$ である。従って

$$
z\in N_H(x)\setminus\{y\},
\qquad
w\in N_H(y)\setminus\{x\}
$$

を取れる。三角形禁止と $4$-cycle 禁止により、非隣接性を介して

$$
d_H(x)=d_H(w)=d_H(z)=d_H(y)
$$

を得る。よって $H$ は正則である。

### 補題 2.4：位数 $19$ の回転はただ一つの頂点を固定する

$$
|\operatorname{Fix}(r)|=1.
$$

#### 証明

頂点数について

$$
3250\equiv1\pmod{19}
$$

なので、$r$ の固定点数は $1$ modulo $19$ であり、少なくとも一つある。

もし $|H|>1$ なら、補題 2.3 と Moore graph の一意共通近傍性により、$H$ は次数 $19,38,57$ の Moore graph になる。次数 $19,38$ は既知事実 1.2 に反する。次数 $57$ なら、$H$ の任意の頂点の全近傍が $H$ に入り、$\Gamma$ の連結性から $H=V(\Gamma)$ となる。すると $r=1$ であり、$r$ の位数 $19$ に反する。

従って $|H|=1$ である。

### 系 2.5：唯一固定点は $D_{19}$ 全体で固定される

$r$ の唯一固定点を $u$ とする。このとき任意の $g\in D_{19}$ について

$$
g(u)=u.
$$

#### 証明

$\langle r\rangle$ は $D_{19}$ の正規部分群である。従って $g(u)$ も $r$ の固定点である。固定点は一つなので $g(u)=u$。

---

## 3. 枝、fiber、完全マッチング

### 定義 3.1：枝と branch fiber

$u$ の近傍を枝と呼ぶ。

$$
N(u)=\{b\in V(\Gamma):u\sim b\}.
$$

枝 $b\in N(u)$ に対して、

$$
L_b=\{x\in V(\Gamma):x\ne u\ \text{and}\ b\sim x\}
$$

と定める。ただし $b$ は $u$ に隣接しているので、三角形禁止により $L_b$ の点は自動的に $u$ と非隣接である。Lean の `branchFiber Γ u b` はこの集合に対応する。

より明示的には、距離 $2$ の側だけを使って

$$
L_b=\{x:d(u,x)=2,\ x\sim b\}
$$

としても同じである。

### 補題 3.2：距離 $2$ 頂点の fiber 分解

$$
V(\Gamma)=\{u\}\sqcup N(u)\sqcup\bigsqcup_{b\in N(u)}L_b.
$$

また、各 $b$ について

$$
|L_b|=56.
$$

#### 証明

$|N(u)|=57$。枝 $b$ の近傍は $57$ 個で、その一つが $u$ であるから $|L_b|=56$。

距離 $2$ の点 $x$ は $u$ と非隣接であるため、$\mu=1$ により $u,x$ は一意の共通近傍 $b$ を持つ。従って $x\in L_b$ であり、この $b$ は一意である。

### 補題 3.3：異なる fiber 間の完全マッチング

$b,c\in N(u)$, $b\ne c$ とする。このとき $L_b$ と $L_c$ の間の辺は完全マッチングである。

#### 証明

$x\in L_b$ を取る。$x$ と $c$ は非隣接である。もし $x\sim c$ なら、$u,x$ は $b,c$ という二つの共通近傍を持つからである。

従って $x,c$ は非隣接であり、$\mu=1$ により一意の共通近傍 $y$ を持つ。$y$ は $c$ に隣接し、かつ $u$ とは距離 $2$ にあるので $y\in L_c$ である。これで $x$ から $L_c$ への隣接点の存在と一意性が出る。逆向きも同様である。

Lean では、片側一意性

```lean
∃! y, y ∈ branchFiber Γ u c ∧ Γ.Adj x y
```

を先に証明し、両側版をまとめるのがよい。

---

## 4. 枝集合上の $D_{19}$ 作用

### 補題 4.1：枝は三つの $r$-周期に分かれる

$r$ は $N(u)$ 上に固定点を持たない。従って

$$
N(u)=A\sqcup B\sqcup C
$$

と分解でき、

$$
A=\{a_i:i\in\mathbb Z/19\},
\quad
B=\{b_i:i\in\mathbb Z/19\},
\quad
C=\{c_i:i\in\mathbb Z/19\},
$$

かつ

$$
r(a_i)=a_{i+1},\quad
r(b_i)=b_{i+1},\quad
r(c_i)=c_{i+1}
$$

が成り立つ。

#### 証明

もし枝 $b$ が $r$ で固定されれば、$b$ は $r$ の固定頂点となる。しかし $r$ の固定頂点は $u$ ただ一つであり、$b\ne u$。矛盾。

従って $57$ 本の枝は長さ $19$ の orbit 三つに分かれる。

### 補題 4.2：反射は一つの枝周期を反転し、残り二つを交換する

添字を取り直すと、

$$
t(a_i)=a_{-i},
\qquad
 t(b_i)=c_{-i},
\qquad
 t(c_i)=b_{-i}
$$

である。

#### 証明

$t$ は $u$ を固定する。$\operatorname{Fix}(t)$ は $K_{1,55}$ である。

もし $u$ が固定 star の中心なら、$u$ の近傍のうち $55$ 個が $t$ で固定される。しかし $N(u)$ は三つの $19$-cycle に分かれており、反射が各 $19$-cycle 内で固定できる点は高々一つである。合計高々三つなので矛盾。

従って $u$ は固定 star の葉であり、中心は $N(u)$ のある枝である。それを $a_0$ と呼ぶ。この枝を含む周期を $A$ とし、添字を選べば

$$
t(a_i)=a_{-i}
$$

である。

残り二つの $19$-cycle を $t$ が個別に保存したと仮定すると、それぞれに固定枝が一つずつ生じる。すると $u$ は固定集合内で $a_0$ とそれらの固定枝に隣接するため、固定 star 内次数が少なくとも三になる。star の葉は固定集合内次数一しか持たないから、$u$ が中心でなければならない。しかし上で $u$ は中心でないと示した。矛盾。

従って残り二つの周期は交換される。添字を調整して

$$
t(b_i)=c_{-i},
\qquad
 t(c_i)=b_{-i}
$$

を得る。

### 系 4.3：頂点軌道構造

$D_{19}$ の頂点集合上の orbit 構造は

$$
1^1,
\qquad
19^{55},
\qquad
38^{58}
$$

である。

#### 証明

$u$ が一つの固定 orbit を与える。

枝では、$A$ が size $19$ orbit、$B\cup C$ が size $38$ orbit を与える。

$A$-fiber については、後で定義する反射固定集合の $54$ 点部分が $54$ 個の size $19$ orbit を与え、反射で交換される二点部分が一つの size $38$ orbit を与える。

$B,C$-fiber は反射で交換されるので、各 fiber 座標ごとに size $38$ orbit を与える。座標は $56$ 個である。

従って

$$
1^1,
\quad
19^{1+54}=19^{55},
\quad
38^{1+1+56}=38^{58}.
$$

---

## 5. $A$-fiber 座標と matching permutation

### 定義 5.1：$A$-fiber の座標

以後

$$
L_i=L_{a_i}
$$

と書く。

$L_0$ を $56$ 点集合 $P$ と同一視する。$r^i$ によって

$$
L_i=\{(i,p):p\in P\}
$$

と座標化する。この座標では

$$
r(i,p)=(i+1,p).
$$

$t$ の $L_0$ 上の作用を

$$
\theta:P\to P
$$

と書く。固定 star の中心は $a_0$ であり、固定 star の葉は $u$ と $L_0$ 内の $54$ 点である。従って

$$
P=F\sqcup E,
\qquad
|F|=54,
\qquad
E=\{+,-\},
$$

かつ

$$
\theta|_F=\operatorname{id},
\qquad
\theta(+)=-,
\qquad
\theta(-)=+.
$$

この座標では

$$
t(i,p)=(-i,\theta p).
$$

さらに

$$
t_h=r^htr^{-h}
$$

とおけば、

$$
t_h(i,p)=(2h-i,\theta p).
$$

特に $t_h$ は $L_h$ を保存し、その中の $F$ 型 $54$ 点を固定し、$E$ 型二点を交換する。

### 定義 5.2：matching permutation $A_d$

$d\in\mathbb Z/19$, $d\ne0$ に対して、$L_i$ と $L_{i+d}$ の完全マッチングを置換

$$
A_d\in\operatorname{Sym}(P)
$$

で表す。すなわち、任意の $i,p$ について

$$
(i,p)\sim(i+d,A_d(p)).
$$

この定義が $i$ に依存しないのは、$r$ が自己同型であり、$r$ が fiber index を同時に一つ進めるからである。

無向性から

$$
A_{-d}=A_d^{-1}.
$$

反射対称性から

$$
A_{-d}=\theta A_d\theta.
$$

Lean では、`matchingRotationPerm d i` のように $i$ を残して定義し、その後で rotation equivariance により全て同じ cardinality を持つことを示してもよい。自然言語上は $A_d$ にまとめる。

---

## 6. 中点反射条件と $A$-fiber contribution

### 補題 6.1：中点反射条件

任意の $h\ne0$ と $p\in P$ について、

$$
A_{2h}(p)=\theta p
\quad\Longleftrightarrow\quad
A_h(p)\in E.
$$

#### 証明

$x=(0,p)$ とする。中点反射 $t_h$ は

$$
x=(0,p)
$$

を

$$
t_hx=(2h,	heta p)
$$

へ送る。

まず、$x$ と $t_hx$ が隣接することは、$L_0$ と $L_{2h}$ の matching の定義により

$$
A_{2h}(p)=\theta p
$$

と同値である。

次に、$x$ の $L_h$ 内の隣接点は

$$
(h,A_h(p))
$$

である。この辺を $t_h$ で写すと、$t_hx$ の $L_h$ 内の隣接点は

$$
(h,\theta A_h(p))
$$

である。

従って、$x$ と $t_hx$ が $L_h$ 内に共通近傍を持つことは

$$
A_h(p)=\theta A_h(p)
$$

と同値であり、これは $A_h(p)\in F$ と同値である。

- $A_h(p)\in F$ の場合、$x$ と $t_hx$ は共通近傍を持つ。もし $x\sim t_hx$ なら三角形ができるため、$x$ と $t_hx$ は隣接しない。
- $A_h(p)\in E$ の場合、$L_h$ 内に固定共通近傍はない。もし $x$ と $t_hx$ が非隣接なら、$\mu=1$ により一意の共通近傍 $z$ が存在する。$t_h$ は $x$ と $t_hx$ を交換するため、一意性から $z$ は $t_h$ で固定される。$t_h$ の固定 star は

  $$
  \{a_h,u\}\cup\{(h,f):f\in F\}
  $$

  である。$x,t_hx$ は $u$ にも $a_h$ にも隣接しないので、固定共通近傍があるなら $L_h$ 内の $F$ 型点でなければならない。しかし今は存在しない。従って $x$ と $t_hx$ は隣接する。

以上より同値が従う。

### 定義 6.2：例外集合

$h\ne0$ に対して

$$
S_h=A_h^{-1}(E)
$$

と定める。すると

$$
|S_h|=2.
$$

補題 6.1 より、

$$
S_h=\{p\in P:A_{2h}(p)=\theta p\}.
$$

また、反射対称性から

$$
S_{-h}=\theta(S_h).
$$

### 補題 6.3：例外集合は $E$ と交わらない

任意の $h\ne0$ について

$$
S_h\cap E=\varnothing.
$$

#### 証明

$$
e_h=|S_h\cap E|
$$

とおく。

$p\in S_h\cap E$ とする。補題 6.1 の形

$$
A_{2h}(p)=\theta p
$$

から、$A_{2h}(p)\in E$ である。従って

$$
p\in S_{2h}.
$$

よって

$$
S_h\cap E\subseteq S_{2h}\cap E,
$$

従って

$$
e_h\le e_{2h}.
$$

$\mathbb Z_{19}^{\ast}$ において $h\mapsto2h$ は一つの巡回置換である。実際、

$$
2^9\equiv -1\pmod{19},
$$

なので $2$ の位数は $18$ である。従って全ての $e_h$ は同じ値 $e$ を持つ。

#### $e=1$ の排除

$S_h\cap E=\{p\}$ とする。包含と濃度一定性から、同じ $p$ が

$$
S_h,S_{2h},S_{4h},\ldots
$$

の全てに入る。特に $2^9h=-h$ より $p\in S_{-h}$。

一方、

$$
S_{-h}=\theta(S_h)
$$

なので

$$
S_{-h}\cap E=\{\theta p\}.
$$

$\theta p\ne p$ であるから矛盾。

#### $e=2$ の排除

この場合、全ての $h\ne0$ について $S_h=E$ である。補題 6.1 より、任意の $d\ne0$ について

$$
A_d(+)=-,
\qquad
A_d(-)=+.
$$

従って、任意の $j\ne0$ について $(0,+)$ と $(j,+)$ は隣接しない。

しかし、任意の

$$
k\ne0,j
$$

について、$(k,-)$ は $(0,+)$ と $(j,+)$ の共通近傍である。実際、

$$
A_k(+)=-,
\qquad
A_{k-j}(+)=-.
$$

これは少なくとも $17$ 個の共通近傍を与え、$\mu=1$ に反する。

従って $e=0$ である。

### 補題 6.4：$A_d$ の固定点はちょうど二つである

任意の $d\ne0$ について、

$$
|\operatorname{Fix}(A_d)|=2.
$$

#### 証明

$d=2h$ と書く。$2$ は $\mathbb Z/19$ で可逆なので、この $h$ は一意に存在する。

補題 6.2 と補題 6.3 より、

$$
S_h=\{p:A_d(p)=\theta p\}
\quad\text{かつ}\quad
S_h\subset F.
$$

従って $p\in S_h$ なら $\theta p=p$ なので $A_d(p)=p$。

逆に $A_d(p)=p$ とする。もし $p\in E$ なら $A_d(p)=p\in E$ なので $p\in S_d=A_d^{-1}(E)$ となる。しかし補題 6.3 により $S_d\cap E=\varnothing$。矛盾。従って $p\in F$ であり、$\theta p=p$。よって $A_d(p)=\theta p$ なので $p\in S_h$。

従って

$$
\operatorname{Fix}(A_d)=S_h,
$$

その cardinality は $2$ である。

### 定理 6.5：$A$-fiber contribution は固定された非零 $d$ ごとに $38$ である

非零 $d\in\mathbb Z/19$ に対し、

$$
\left|\{x\in\bigsqcup_iL_i:x\sim r^dx\}\right|=38.
$$

#### 証明

$x=(i,p)\in L_i$ とする。このとき

$$
r^dx=(i+d,p).
$$

matching permutation の定義より、

$$
x\sim r^dx
\quad\Longleftrightarrow\quad
A_d(p)=p.
$$

すなわち、各 fiber $L_i$ における寄与は $\operatorname{Fix}(A_d)$ の濃度に等しい。補題 6.4 よりこれは $2$ である。

fiber は $19$ 個あるので、総寄与は

$$
19\cdot2=38.
$$

#### Lean 化メモ

固定された $d$ に対し、各 $i$ で

```lean
support_complement (matchingRotationPerm d i)
```

を考えるなら、示すべきことは

```lean
∀ i, (support_complement (matchingRotationPerm d i)).card = 2
```

であり、その和として

```lean
∑ i : ZMod 19, 2 = 38
```

を得ることである。これは「固定された $(i,p)$ に対して可能な $d$ が高々二つ」という横方向評価ではない。ここが形式化上の重要点である。

---

## 7. selected orbit base と residual split

この節は、Lean の `OrbitBaseSelectionWitness`、`D19AdjacentMovedDecomposition`、および residual split に対応する。

### 定義 7.1：$B,C$ 側 leaf orbit の base 選択

$L_{b_0}$ の $56$ 個の点を任意に列挙し、

$$
x_q\in L_{b_0}
\qquad(q\in\{1,
\ldots,56\})
$$

と書く。

選んだ base から

$$
B_q=\{r^ix_q:i\in\mathbb Z/19\}
\subseteq\bigsqcup_iL_{b_i}
$$

を作る。また反射コピーとして

$$
C_q=t(B_q)=\{tr^ix_q:i\in\mathbb Z/19\}
\subseteq\bigsqcup_iL_{c_i}
$$

を作る。

このとき

$$
B_q\cup C_q
$$

は一つの $D_{19}$-orbit であり、$B_q$ と $C_q$ は二つの $r$-orbit である。

### 補題 7.2：selected orbit は $B,C$ leaf 全体を disjoint に覆う

$$
\bigsqcup_q(B_q\sqcup C_q)
=
\bigsqcup_iL_{b_i}\sqcup\bigsqcup_iL_{c_i}.
$$

#### 証明

$r^i$ は $L_{b_0}$ を $L_{b_i}$ に全単射で写す。従って、$x_q$ が $L_{b_0}$ を disjoint に列挙していれば、$r^ix_q$ は $L_{b_i}$ を disjoint に列挙する。これを全 $i$ で合わせると、$B_q$ たちは $B$-side leaf 全体を disjoint に覆う。

$t$ は $L_{b_i}$ を $L_{c_{-i}}$ に写すので、$C_q$ たちは $C$-side leaf 全体を disjoint に覆う。

$B$-side fiber と $C$-side fiber は異なる枝に属する fiber なので互いに disjoint である。従って全体の disjoint cover が得られる。

### 定義 7.3：residual とその split

selected $B,C$ leaf orbit の和集合を

$$
\mathcal O_{BC}=\bigsqcup_q(B_q\sqcup C_q)
$$

と書く。residual を

$$
R=V(\Gamma)\setminus\mathcal O_{BC}
$$

と定める。

このとき

$$
R=Z\sqcup A_f
$$

と分解する。ただし

$$
Z=\{u\}\cup N(u),
$$

$$
A_f=\bigsqcup_{i\in\mathbb Z/19}L_{a_i}.
$$

ここで $Z$ は fixed/zero part、$A_f$ は $A$-fiber part である。

### 補題 7.4：residual split

上の定義で

$$
R=Z\sqcup A_f
$$

である。

#### 証明

補題 3.2 より

$$
V(\Gamma)=\{u\}\sqcup A\sqcup B\sqcup C
\sqcup\bigsqcup_iL_{a_i}
\sqcup\bigsqcup_iL_{b_i}
\sqcup\bigsqcup_iL_{c_i}.
$$

補題 7.2 より、selected orbit はちょうど

$$
\bigsqcup_iL_{b_i}\sqcup\bigsqcup_iL_{c_i}
$$

を覆う。従って、その補集合は

$$
\{u\}\sqcup A\sqcup B\sqcup C\sqcup\bigsqcup_iL_{a_i}
=Z\sqcup A_f.
$$

互いに disjoint であることは、branch/fiber 分解の一意性から従う。

### 補題 7.5：zero part の adjacent-moved contribution は $0$

非零 $d$ に対し、

$$
\left|\{x\in Z:x\sim r^dx\}\right|=0.
$$

#### 証明

$u$ については $r^du=u$ であり、単純グラフなので $u\not\sim u$。

枝 $b\in N(u)$ については、$r^db$ も $N(u)$ に属する。さらに $d\ne0$ なので $r^db\ne b$。もし

$$
b\sim r^db
$$

なら、$u,b,r^db$ が三角形を作る。従って不可能である。

### 定理 7.6：fixed/`A`-side contribution は $38$

非零 $d$ に対し、

$$
\left|\{x\in R:x\sim r^dx\}\right|=38.
$$

#### 証明

補題 7.4 により $R=Z\sqcup A_f$。補題 7.5 により $Z$ からの寄与は $0$。定理 6.5 により $A_f$ からの寄与は $38$。従って residual 全体からの寄与は $38$。

#### Lean 化メモ

この定理が、現在 `fixed_or_A_contribution : ∀ d, d ≠ 0 → fixedOrAContribution d = 38` として入力されている部分を置き換えるべき自然言語証明である。

---

## 8. matching permutation と support complement の対応

この節では、形式化で混乱しやすい対応を明示する。

### 定義 8.1：support complement

置換 $\sigma\in\operatorname{Sym}(P)$ に対し、support complement を

$$
\operatorname{Fix}(\sigma)=\{p\in P:\sigma(p)=p\}
$$

と読む。Lean で `support` を「動く点集合」として定義しているなら、その complement が固定点集合である。

### 補題 8.2：固定点と adjacent-moved 頂点の fiberwise bijection

非零 $d$ と index $i$ を固定する。このとき写像

$$
\Phi_i:\operatorname{Fix}(A_d)	o
\{x\in L_i:x\sim r^dx\},
\qquad
p\mapsto(i,p)
$$

は全単射である。

#### 証明

$p\in\operatorname{Fix}(A_d)$ なら $A_d(p)=p$。matching の定義から

$$
(i,p)\sim(i+d,A_d(p))=(i+d,p)=r^d(i,p).
$$

従って $\Phi_i(p)$ は右辺集合に入る。

逆に、$x=(i,p)\in L_i$ が $x\sim r^dx$ を満たすなら

$$
(i,p)\sim(i+d,p).
$$

$L_i$ と $L_{i+d}$ の matching は一意なので、

$$
A_d(p)=p.
$$

従って $p\in\operatorname{Fix}(A_d)$。単射性は座標表示の一意性から従う。

### 系 8.3：support complement の総和と $A$-fiber contribution

非零 $d$ について

$$
\sum_{i\in\mathbb Z/19}|\operatorname{Fix}(A_d)|
=
\left|\{x\in A_f:x\sim r^dx\}\right|.
$$

補題 6.4 により左辺は

$$
19\cdot2=38.
$$

---

## 9. trace/character argument

### 定義 9.1：固定点数と adjacent-moved 数

自己同型 $g$ に対して

$$
a_0(g)=|\operatorname{Fix}(g)|,
$$

$$
a_1(g)=|\{x:x\sim g(x)\}|
$$

とおく。

### 補題 9.2：Higman 型跡公式

$7$-固有空間上の指標を $\chi_7(g)$ とすると、

$$
\chi_7(g)=\frac{8a_0(g)+a_1(g)-65}{15}.
$$

#### 証明

$7$-固有空間への射影は

$$
E_7=\frac{A+8I}{15}-\frac{J}{750}
$$

である。置換行列を $P_g$ とすると、

$$
\chi_7(g)=\operatorname{Tr}(E_7P_g).
$$

ここで

$$
\operatorname{Tr}(IP_g)=a_0(g),
$$

$$
\operatorname{Tr}(AP_g)=a_1(g),
$$

$$
\operatorname{Tr}(JP_g)=3250.
$$

従って

$$
\chi_7(g)
=\frac{a_1(g)+8a_0(g)}{15}-\frac{3250}{750}
=\frac{a_1(g)+8a_0(g)-65}{15}.
$$

### 補題 9.3：反射の $a_1$ 値

反射 $t$ について

$$
a_0(t)=56,
\qquad
 a_1(t)=112.
$$

#### 証明

$a_0(t)=56$ は固定集合が $K_{1,55}$ であることから従う。

固定 star の中心を $c$ とする。中心 $c$ は固定葉 $55$ 個に隣接しているので、固定集合の外へ出る辺は $57-55=2$ 本である。各固定葉は中心 $c$ にだけ固定集合内で隣接するので、固定集合の外へ $57-1=56$ 本の辺を出す。

従って固定集合から非固定集合へ出る辺数は

$$
2+55\cdot56=3082.
$$

非固定頂点数は

$$
3250-56=3194,
$$

従って $t$ の二点 orbit は $1597$ 個である。

二点 orbit $\{x,tx\}$ が非隣接なら、$\mu=1$ により $x,tx$ の一意の共通近傍が存在し、それは $t$ で固定される。この場合、固定集合からこの二点 orbit へ二本の辺が出る。逆に $x\sim tx$ なら、三角形禁止により固定共通近傍はない。

よって非隣接二点 orbit の数は

$$
3082/2=1541.
$$

従って隣接二点 orbit の数は

$$
1597-1541=56.
$$

各隣接二点 orbit は $a_1(t)$ に二頂点分寄与するので

$$
a_1(t)=2\cdot56=112.
$$

### 補題 9.4：$D_{19}$ の有理表現分解

$D_{19}$ の有理既約表現として、

$$
\mathbf 1,
\qquad
\varepsilon,
\qquad
\rho
$$

を使う。ここで $\varepsilon$ は反射に $-1$ を与える一次元表現、$\rho$ は $18$ 次元の cyclotomic 型有理既約表現であり、

$$
\rho(r^d)=-1\quad(d\ne0),
\qquad
\rho(tr^d)=0.
$$

頂点置換表現は、系 4.3 より

$$
\pi=114\mathbf1+58\varepsilon+171\rho.
$$

#### 証明

size $1$ orbit は $\mathbf1$ を与える。

size $19$ orbit は $D_{19}/\langle t\rangle$ 型であり、

$$
\mathbf1+\rho
$$

を与える。

size $38$ orbit は正則表現であり、

$$
\mathbf1+\varepsilon+2\rho
$$

を与える。

系 4.3 の

$$
1^1,
\quad
19^{55},
\quad
38^{58}
$$

を代入すると、

$$
\pi
=1\cdot\mathbf1+55(\mathbf1+\rho)+58(\mathbf1+\varepsilon+2\rho)
=114\mathbf1+58\varepsilon+171\rho.
$$

### 補題 9.5：非自明回転の $a_1$ 可能値

任意の $d\ne0$ について

$$
a_1(r^d)\in\{57,342,627,912\}.
$$

#### 証明

$7$-固有空間上の表現を

$$
\chi_7=\alpha\mathbf1+\beta\varepsilon+\gamma\rho
$$

と書く。

次元から

$$
\alpha+\beta+18\gamma=1729.
$$

反射 $t$ について、補題 9.2 と補題 9.3 より

$$
\chi_7(t)=\frac{8\cdot56+112-65}{15}=33.
$$

一方、表現側では

$$
\chi_7(t)=\alpha-\beta.
$$

従って

$$
\alpha-\beta=33.
$$

非零 $d$ について、補題 2.4 より

$$
a_0(r^d)=1.
$$

補題 9.2 より

$$
\chi_7(r^d)=\frac{a_1(r^d)-57}{15}.
$$

表現側では

$$
\chi_7(r^d)=\alpha+\beta-\gamma.
$$

ここで $\gamma=91-s$ と書くと、上の二つの線形方程式から

$$
\alpha=62+9s,
\qquad
\beta=29+9s,
\qquad
\gamma=91-s
$$

となる。また

$$
a_1(r^d)=57+285s.
$$

$(-8)$-固有空間は

$$
\pi-\mathbf1-\chi_7
$$

である。補題 9.4 を使うと、その係数は

$$
(51-9s)\mathbf1+(29-9s)\varepsilon+(80+s)\rho.
$$

非負性と $a_1(r^d)\ge0$ から

$$
s=0,1,2,3.
$$

従って

$$
a_1(r^d)
=57+285s
\in\{57,342,627,912\}.
$$

### 系 9.6：$B,C$ 側寄与は各非零 $d$ に対し少なくとも $8$ orbit

非零 $d$ を固定する。定理 7.6 により residual/fixed-`A` 側寄与は $38$ である。selected $B,C$ leaf orbit は、各 $q$ について寄与するなら二つの $r$-orbit から合計 $38$ 頂点分寄与し、寄与しないなら $0$ である。

従ってある整数 $N_d$ が存在して

$$
a_1(r^d)=38+38N_d.
$$

補題 9.5 の可能値のうち、右辺の形を満たすのは

$$
342=38+38\cdot8
$$

または

$$
912=38+38\cdot23
$$

だけである。従って

$$
N_d\ge8.
$$

Lean では、この $N_d$ は

$$
N_d=
\left|\{q:d\in D_q\}\right|
$$

として実装するのが自然である。

---

## 10. $B,C$ 側 difference set と最終矛盾

### 定義 10.1：内部 difference set

selected base $x_q\in L_{b_0}$ から得られる $B$ 側 orbit を

$$
W_q(i)=r^ix_q
$$

と書く。内部 difference set を

$$
D_q=\{d\in\mathbb Z/19:d\ne0\text{ and }W_q(i)\sim W_q(i+d)\text{ for all }i\}
$$

と定める。

$r$ が自己同型なので、ある一つの $i$ で成り立てば全ての $i$ で成り立つ。無向性により

$$
d\in D_q\Rightarrow -d\in D_q.
$$

### 補題 10.2：各 $D_q$ のサイズは高々 $2$

$$
|D_q|\le2.
$$

#### 証明

もし $a,b\in D_q$ かつ $a\ne\pm b$ なら、次の四頂点を考える。

$$
W_q(0),
\quad
W_q(a),
\quad
W_q(a+b),
\quad
W_q(b).
$$

差がそれぞれ

$$
a,
\quad
b,
\quad
-a,
\quad
-b
$$

であるため、これらは順に隣接する。すなわち $4$-cycle ができる。

四頂点が相異なることは、$a,b\ne0$ および $a\ne\pm b$ から従う。これは補題 1.5 に反する。

従って $D_q$ は高々一つの符号対 $\{d,-d\}$ しか含めず、

$$
|D_q|\le2.
$$

### 定理 10.3：$D_{19}$ 作用は存在しない

$D_{19}$ は $\operatorname{Aut}(\Gamma)$ の部分群として作用できない。

#### 証明

系 9.6 より、任意の非零 $d$ について

$$
\left|\{q:d\in D_q\}\right|\ge8.
$$

従って

$$
\sum_{d\ne0}\left|\{q:d\in D_q\}\right|
\ge18\cdot8=144.
$$

一方、和の順序を入れ替えると

$$
\sum_{d\ne0}\left|\{q:d\in D_q\}\right|
=
\sum_q |D_q|.
$$

補題 10.2 より各 $|D_q|\le2$ であり、$q$ は $56$ 個なので

$$
\sum_q |D_q|\le56\cdot2=112.
$$

よって

$$
144\le112
$$

という矛盾が得られる。

### 系 10.4：自己同型群が $D_{19}$ である場合も不可能

特に

$$
\operatorname{Aut}(\Gamma)\simeq D_{19}
$$

は不可能である。

#### 証明

もし $\operatorname{Aut}(\Gamma)\simeq D_{19}$ なら、$D_{19}$ が自己同型群に部分群として作用する。これは定理 10.3 に反する。

---

## 11. Lean 形式化の依存順序

以下の順序で補題化すると、現在の強い入力を段階的に削れる。

### Phase A：Moore graph 基本補題

1. `no_triangle`。
2. `no_four_cycle`。
3. `branchFiber_card`。
4. `existsUnique_branch_of_not_adj_center`。
5. `existsUnique_adjacent_between_branchFibers`。

これらは SRG パラメータ $(3250,57,0,1)$ から直接得る。

### Phase B：回転固定点と枝作用

1. `rotation_fixed_card_eq_one`。
2. `center_fixed_by_D19`。
3. `neighbor_orbits_three_cycles`。
4. `reflection_branch_action_A_BC`。
5. `vertex_orbit_structure_1_19_38`。

外部入力として、involution の固定点集合が star であることを使う。

### Phase C：$A$-fiber matching

1. $A$-fiber coordinate `L_i = r^i L_0`。
2. `theta` の固定点分解 $P=F\sqcup E$。
3. matching permutation `A_d` の構成。
4. `middle_reflection_criterion`：

   $$
   A_{2h}(p)=\theta p\Longleftrightarrow A_h(p)\in E.
   $$

5. `exception_disjoint_E`：$S_h\cap E=\varnothing$。
6. `matching_fixed_card_two`：$|\operatorname{Fix}(A_d)|=2$。
7. `a_fiber_contribution_eq_38`。

この Phase C が、Codex コメントで指摘された「A-fiber cardinality 38 boundary」の本体である。

### Phase D：selected orbit base と residual split

1. $L_{b_0}$ の $56$ 点を base として選ぶ。
2. $B_q,C_q$ を生成する。
3. `selected_orbits_cover_BC_leaf`。
4. `residual_eq_zeroPart_union_aPart`。
5. `zeroPart_contribution_zero`。
6. `fixed_or_A_contribution_eq_38`。
7. `adjacentMovedDecomposition` を構成する。

ここで `fixedOrAContribution` は入力ではなく定理になる。

### Phase E：trace/character

1. `higman_trace_formula`。
2. `reflection_a1_eq_112`。
3. `vertex_permutation_representation_decomposition`。
4. `rotation_a1_possible_values`。
5. `Nd_lower`：各非零 $d$ に対し $N_d\ge8$。

### Phase F：最終計数

1. `internalDiffSet_symm`。
2. `Dq_card_le_two_of_moore`。
3. `counting_contradiction_zmod`。

この部分は既に Lean でかなり切り出しやすい。

---

## 12. 既存の強い仮定との対応

### `D19FinalInputs.fixed_or_A_contribution`

置換対象：定理 7.6。

現在の入力

```lean
∀ d : ZMod 19, d ≠ 0 → fixedOrAContribution d = 38
```

は、次の二つの補題から得る。

1. `zeroPart_contribution_zero`。
2. `a_fiber_contribution_eq_38`。

### `D19AdjacentMovedDecomposition`

置換対象：補題 7.2、補題 7.4、補題 7.5、定理 7.6。

selected orbit base が $B,C$ leaf 全体を覆い、補集合が $Z\sqcup A_f$ であることを使う。

### `D19ActionConcreteData.a1_contribution`

置換対象：系 9.6 と selected orbit base の definition。

具体的には、

$$
a_1(r^d)=38+38\cdot |\{q:d\in D_q\}|
$$

を示す。ここで最初の $38$ は residual/fixed-`A` 側、後半は selected $B,C$ leaf orbit 側である。

### `OrbitBaseSelectionWitness`

置換対象：定義 7.1 と補題 7.2。

$L_{b_0}$ の $56$ 点を列挙すれば、$r$ と $t$ の作用により $B,C$ leaf orbit 全体の base が得られる。

---

## 13. 検証メモ

### 13.1 固定 star の中心は $u$ ではない

ここを誤ると即座に偽の矛盾が出る。$u$ が中心なら $55$ 本の枝が反射で固定される必要があるが、枝上の反射固定点は高々三つである。正しくは、固定 star の中心は $a_0$、$u$ はその葉である。

### 13.2 residual は selected $B,C$ leaf orbit の補集合として定義する

residual を曖昧にすると、枝集合 $N(u)$ の扱いが崩れる。枝は非零回転で動くが、adjacent-moved contribution は常に $0$ である。従って residual split では、枝を `zeroPart` に入れるのが安全である。

### 13.3 $38$ は trace から直接出るのではない

trace/character argument は、全体の $a_1(r^d)$ の可能値を制限する。$A$-fiber contribution $38$ は、中点反射と matching permutation の固定点数 $2$ から独立に得る。ここを混同しない。

### 13.4 $A$-fiber contribution は縦方向評価である

固定された $d$ に対し、全 $19$ fiber で support complement を足す。各 fiber で二点、合計 $38$ である。

### 13.5 最終矛盾は $B,C$ leaf orbit の difference set にだけ適用する

$D_q$ は selected $B,C$ leaf orbit から作る。$B,C$ 枝 orbit や $A$ exceptional orbit は selected base に入れない。これらは residual/zero-or-A 側に入り、非零回転の adjacent-moved contribution には寄与しない。

---

## 14. 結論

Moore graph $\Gamma$ of degree $57$ and diameter $2$ に $D_{19}$ が自己同型として作用すると仮定すると、回転固定点 $u$ の周りの枝と fiber は極めて rigid な構造を持つ。

一次的な orbit 分解

$$
1^1,
\quad
19^{55},
\quad
38^{58}
$$

だけでは矛盾しない。しかし、$A$-fiber 間の完全マッチングを中点反射で調べると、各非零回転 $r^d$ に対する fixed/`A`-side contribution が必ず

$$
38
$$

になる。

一方、trace/character argument により、残る $B,C$ leaf 側では各非零差 $d$ について少なくとも $8$ 個の selected orbit が寄与する必要がある。これは合計で少なくとも

$$
18\cdot8=144
$$

の difference membership を要求する。

しかし、各 selected orbit の internal difference set は $4$-cycle 禁止により高々二点しか持たないので、全体では高々

$$
56\cdot2=112
$$

である。矛盾。

従って

$$
D_{19}\not\leq\operatorname{Aut}(\Gamma).
$$

特に

$$
\operatorname{Aut}(\Gamma)\simeq D_{19}
$$

は不可能である。
