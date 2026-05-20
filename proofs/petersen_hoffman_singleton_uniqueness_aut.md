# Petersen graph と Hoffman–Singleton graph
## 一意性と自己同型群の決定

このノートでは、強正則グラフの文脈で次の二つの古典的事実をまとめる。

| graph | 強正則パラメータ | 自己同型群 |
|---|---:|---:|
| Petersen graph | \((10,3,0,1)\) | \(S_5\), 位数 \(120\) |
| Hoffman–Singleton graph | \((50,7,0,1)\) | \(P\Sigma U_3(5) \cong PSU_3(5):2\), 位数 \(252000\) |

ここで \(PSU_3(5)\) は、慣例的に \(\mathbb F_{25}/\mathbb F_5\) 上の 3 次元射影特殊ユニタリ群を表す。したがって

\[
|PSU_3(5)|=
\frac{5^3(5^3+1)(5^2-1)}{\gcd(3,5+1)}
=126000,
\]

であり、半線形な外部自己同型を 1 個加えると full automorphism group の位数は \(252000\) になる。

---

## 1. 共通の準備：\(\operatorname{srg}(v,k,0,1)\) と Moore graph

単純無向グラフ \(\Gamma\) が強正則グラフ \(\operatorname{srg}(v,k,\lambda,\mu)\) であるとは、

- 頂点数が \(v\)；
- 各頂点の次数が \(k\)；
- 隣接する 2 頂点の共通隣接点数が \(\lambda\)；
- 隣接しない 2 頂点の共通隣接点数が \(\mu\)；

であることをいう。隣接行列を \(A\)、全 1 行列を \(J\) とすると、

\[
A^2=kI+\lambda A+\mu(J-I-A)
\]

である。特に \((\lambda,\mu)=(0,1)\) なら

\[
A^2+A=(k-1)I+J.\tag{1}
\]

また強正則パラメータの基本関係式

\[
k(k-1-\lambda)=\mu(v-k-1)
\]

から、\(\lambda=0,\mu=1\) の場合

\[
v=k^2+1
\]

が従う。

この場合、グラフは三角形を持たない。さらに、隣接しない 2 頂点はちょうど 1 個の共通隣接点を持つので、直径は 2 である。4-cycle があると、対角の 2 頂点が 2 個の共通隣接点を持ってしまうため、4-cycle も存在しない。したがって \(k\ge 2\) では girth は 5 であり、これは直径 2 の Moore graph と同じ構造である。

---

# Part I. Petersen graph

## 2. Petersen graph の構成

Petersen graph は Kneser graph \(KG(5,2)\) として定義できる。

頂点集合を

\[
V=\binom{\{1,2,3,4,5\}}{2}
\]

とし、2 点 \(A,B\in V\) を

\[
A\sim B \quad\Longleftrightarrow\quad A\cap B=\varnothing
\]

で隣接させる。

### 強正則性の確認

頂点数は \(\binom52=10\)。頂点 \(A=\{a,b\}\) に隣接する頂点は、残り 3 点から 2 点を選ぶものなので

\[
k=\binom32=3.
\]

隣接する 2 頂点 \(A,B\) は互いに素な 2-subset である。このとき \(A\cup B\) は 4 点集合なので、両方と互いに素な 2-subset は存在しない。したがって

\[
\lambda=0.
\]

一方、隣接しない 2 頂点 \(A,B\) は 1 点を共有する。\(A\cup B\) は 3 点集合であり、その補集合は 2 点集合である。この 2 点集合が \(A\) と \(B\) の両方に互いに素な唯一の頂点である。したがって

\[
\mu=1.
\]

よって Petersen graph は

\[
\operatorname{srg}(10,3,0,1)
\]

である。

---

## 3. Petersen graph の一意性

次を示す。

> **定理.** 任意の \(
> \operatorname{srg}(10,3,0,1)
> \) は Petersen graph と同型である。

### 証明

\(\Gamma\) を \(\operatorname{srg}(10,3,0,1)\) とする。頂点 \(\infty\) を 1 つ固定し、その近傍を

\[
N(\infty)=\{a_1,a_2,a_3\}
\]

と書く。\(\lambda=0\) なので、\(a_1,a_2,a_3\) の間に辺はない。

各 \(a_i\) は次数 3 であり、すでに \(\infty\) に隣接している。したがって \(a_i\) には、\(\infty\) 以外に 2 個の隣接点がある。それを

\[
S_i=N(a_i)\setminus\{\infty\}
=\{x_i,y_i\}
\]

と書く。

\(\mu=1\) より、\(\infty\) と隣接しない各頂点は \(\infty\) とただ 1 個の共通隣接点を持つ。したがって \(S_1,S_2,S_3\) は互いに交わらず、残り 6 頂点をちょうど分割する。

同じ \(S_i\) の中には辺がない。もし \(x_i\sim y_i\) なら \(a_i,x_i,y_i\) が三角形を作るからである。

次に、異なる \(i,j\) について、\(S_i\) と \(S_j\) の間の辺を考える。\(S_i\) の各頂点は、すでに \(a_i\) に隣接している。次数は 3 なので、残り 2 本の辺は \(S_j,S_k\) に向かう必要がある。しかも \(S_i\) の 1 頂点が \(S_j\) の 2 頂点に隣接すると、\(a_j\) とともに 4-cycle ができる。したがって \(S_i\) と \(S_j\) の間の辺は完全マッチングである。

ラベルを入れ替えて、

\[
x_1\sim x_2,
\qquad
 y_1\sim y_2
\]

および

\[
x_1\sim x_3,
\qquad
 y_1\sim y_3
\]

としてよい。すると \(S_2\) と \(S_3\) の間のマッチングは強制される。もし

\[
x_2\sim x_3,
\qquad
 y_2\sim y_3
\]

なら、\(x_1,x_2,x_3\) が三角形を作ってしまう。したがって必ず

\[
x_2\sim y_3,
\qquad
 y_2\sim x_3
\]

である。

以上で全ての辺が一意に決まった。このグラフは Petersen graph の標準的な 10 頂点表示と同型である。よって \(\operatorname{srg}(10,3,0,1)\) は一意である。\(\square\)

---

## 4. Petersen graph の自己同型群

> **定理.** Petersen graph \(P\) の自己同型群は
> \[
> \operatorname{Aut}(P)\cong S_5
> \]
> である。

### 証明

Petersen graph を \(KG(5,2)\) として見る。\(S_5\) は基礎集合 \(\{1,2,3,4,5\}\) を置換することで 2-subset 全体に作用し、互いに素であるという関係を保つ。したがって

\[
S_5\le \operatorname{Aut}(P).
\]

逆向きに、任意の自己同型がこの形で来ることを示す。

Petersen graph の独立集合は、\(KG(5,2)\) の言葉では、互いに交わる 2-subset の族である。サイズ 4 の独立集合はちょうど

\[
C_i=\{\{i,j\}:j\ne i\}
\qquad (i=1,\dots,5)
\]

の 5 個である。

実際、4 個の 2-subset が互いに交わっているとする。もし全てが共通の点を含むなら、それは上の \(C_i\) である。共通点を持たない場合、たとえば \(\{1,2\}\) と \(\{1,3\}\) を含むなら、それらの両方に交わり、かつ全体の共通点を作らない 2-subset は高々 \(\{2,3\}\) であり、サイズ 4 にはならない。よってサイズ 4 の独立集合は上の 5 個だけである。

したがって任意の自己同型は 5 個の最大独立集合

\[
C_1,\dots,C_5
\]

を置換する。これにより準同型

\[
\Phi:\operatorname{Aut}(P)\to S_5
\]

が得られる。

この \(\Phi\) は単射である。なぜなら、頂点 \(\{i,j\}\) は

\[
C_i\cap C_j=\{\{i,j\}\}
\]

として復元できるからである。最大独立集合への作用が自明なら、全頂点への作用も自明である。

すでに \(S_5\le\operatorname{Aut}(P)\) があるので、

\[
\operatorname{Aut}(P)\cong S_5.
\]

\(\square\)

---

# Part II. Hoffman–Singleton graph

## 5. Hoffman–Singleton graph の構成

\(\mathbb F_5\) 上で次の 50 頂点を考える。

\[
V_0=\{p_{x,y}:x,y\in\mathbb F_5\},
\qquad
V_1=\{\ell_{m,c}:m,c\in\mathbb F_5\}.
\]

頂点 \(p_{x,y}\) を「点」、\(\ell_{m,c}\) を「直線 \(y=mx+c\)」と見る。ただし vertical line は直線頂点としては入れない。

隣接関係を次で定める。

1. 同じ vertical class の点について
   \[
   p_{x,y}\sim p_{x,y'}
   \quad\Longleftrightarrow\quad
   y-y'=\pm1.
   \]
   これは各 \(x\) ごとに 5-cycle を作る。

2. 同じ slope の直線について
   \[
   \ell_{m,c}\sim \ell_{m,c'}
   \quad\Longleftrightarrow\quad
   c-c'=\pm2.
   \]
   これは各 \(m\) ごとに pentagram、すなわち別の 5-cycle を作る。

3. 点と直線について
   \[
   p_{x,y}\sim \ell_{m,c}
   \quad\Longleftrightarrow\quad
   y=mx+c.
   \]

これは Robertson の pentagon–pentagram 構成と同じである。5 個の pentagon、5 個の pentagram、それらの間の biaffine incidence を合わせた構成である。

---

## 6. Hoffman–Singleton graph が \(\operatorname{srg}(50,7,0,1)\) であること

頂点数は \(25+25=50\)。点 \(p_{x,y}\) は、同じ vertical class の 2 点と、\(m\in\mathbb F_5\) ごとに 1 本ずつ、合計 5 本の直線 \(\ell_{m,y-mx}\) に隣接する。したがって次数は

\[
2+5=7.
\]

直線頂点も同様に、同じ slope class の 2 本と、5 個の点に隣接するので次数 7 である。

### \(\lambda=0\)

隣接する 2 頂点の型で場合分けする。

#### 点—点

隣接する 2 点は

\[
p_{x,y},\ p_{x,y\pm1}
\]

である。同じ 5-cycle 内に共通隣接点はない。また同じ vertical line 上の異なる 2 点を通る非 vertical な直線 \(y=mx+c\) は存在しない。したがって共通隣接点はない。

#### 直線—直線

隣接する 2 直線は

\[
\ell_{m,c},\ \ell_{m,c\pm2}
\]

である。同じ pentagram 内に共通隣接点はない。また平行な異なる 2 直線は交わらない。したがって共通隣接点はない。

#### 点—直線

\(p_{x,y}\sim \ell_{m,c}\)、つまり \(y=mx+c\) とする。共通隣接点が点型なら、それは \(p_{x,y\pm1}\) である必要があるが、これは \(\ell_{m,c}\) 上にない。共通隣接点が直線型なら、それは \(\ell_{m,c\pm2}\) である必要があるが、これは \(p_{x,y}\) を通らない。よって共通隣接点はない。

以上より \(\lambda=0\)。

### \(\mu=1\)

隣接しない 2 頂点について、共通隣接点が一意であることを示す。

#### 点—点、同じ vertical class

\(p_{x,y}\) と \(p_{x,y'}\) が隣接しないなら \(y-y'=\pm2\)。5-cycle 内で距離 2 の 2 点は、ただ 1 個の共通隣接点を持つ。

#### 点—点、異なる vertical class

\(x\ne x'\) のとき、2 点

\[
p_{x,y},\ p_{x',y'}
\]

を通る非 vertical な直線は一意であり、

\[
m=\frac{y-y'}{x-x'},
\qquad
c=y-mx
\]

で与えられる。したがって共通隣接点は \(\ell_{m,c}\) ただ 1 個である。

#### 直線—直線、同じ slope class

\(\ell_{m,c}\) と \(\ell_{m,c'}\) が隣接しないなら \(c-c'=\pm1\)。pentagram、すなわち 5-cycle の中で距離 2 の 2 点は、ただ 1 個の共通隣接点を持つ。

#### 直線—直線、異なる slope class

\(m\ne m'\) のとき、2 直線

\[
y=mx+c,
\qquad
 y=m'x+c'
\]

は \(\mathbb F_5\) 上で一意に交わる。交点は

\[
x=\frac{c'-c}{m-m'},
\qquad
 y=mx+c
\]

である。したがって共通隣接点は対応する点 \(p_{x,y}\) ただ 1 個である。

#### 点—直線、非 incident

\(p_{x,y}\) と \(\ell_{m,c}\) が隣接しないとする。

\[
\delta=y-(mx+c)\in\mathbb F_5^*
\]

とおく。\(\mathbb F_5^*=\{\pm1,\pm2\}\) なので、次の二つの場合に分かれる。

- \(\delta=\pm1\) のとき、\(\ell_{m,c}\) 上の点 \(p_{x,mx+c}\) は \(p_{x,y}\) と同じ vertical 5-cycle で隣接している。これが唯一の共通隣接点である。
- \(\delta=\pm2\) のとき、\(p_{x,y}\) を通る直線 \(\ell_{m,c+\delta}\) は \(\ell_{m,c}\) と同じ slope class の pentagram で隣接している。これが唯一の共通隣接点である。

したがって \(\mu=1\)。

以上より、この構成は

\[
\operatorname{srg}(50,7,0,1)
\]

を与える。

---

## 7. Hoffman–Singleton graph の一意性

次を示す。

> **定理.** 任意の \(
> \operatorname{srg}(50,7,0,1)
> \) は Hoffman–Singleton graph と同型である。

証明は Petersen graph の一意性と同じ「根を固定して層に分ける」方法から始まるが、各 fiber のサイズが 6 になるため、fiber 間の完全マッチングを \(S_6\) の置換として制御する必要がある。

---

### 7.1 層分解

\(\Gamma\) を \(\operatorname{srg}(50,7,0,1)\) とし、頂点 \(\infty\) を固定する。

\[
N(\infty)=\{a_1,\dots,a_7\}
\]

と書く。\(\lambda=0\) なので、\(a_1,\dots,a_7\) の間に辺はない。

各 \(a_i\) について

\[
S_i=N(a_i)\setminus\{\infty\}
\]

とおく。各 \(S_i\) は 6 点集合である。\(\mu=1\) より、\(S_1,\dots,S_7\) は互いに交わらず、\(\infty\) とその近傍以外の 42 頂点を分割する。

同じ \(S_i\) の中に辺はない。異なる \(S_i,S_j\) の間では、各頂点はちょうど 1 本の辺で相手側に接続する。したがって \(S_i\) と \(S_j\) の間の辺は完全マッチングである。

各 \(S_i\) を

\[
S_i=\{(i,1),\dots,(i,6)\}
\]

とラベルする。\(S_i\) から \(S_j\) への完全マッチングは置換行列、すなわち置換

\[
P_{ij}\in S_6
\]

で表される：

\[
(i,t)\sim (j,P_{ij}(t)).
\]

対称性より

\[
P_{ji}=P_{ij}^{-1}.
\]

各 fiber 内のラベルを取り替えることで、標準化して

\[
P_{1j}=P_{j1}=I
\qquad (j=2,\dots,7)
\tag{2}
\]

としてよい。

---

### 7.2 ブロック行列方程式

\(S_1\cup\cdots\cup S_7\) 上の誘導隣接行列を、\(7\times7\) 個の \(6\times6\) block からなる行列

\[
B=(B_{ij})
\]

として書く。ただし

\[
B_{ii}=0,
\qquad
B_{ij}=P_{ij}\quad (i\ne j).
\]

式 (1) をこの層分解に適用すると、異なる \(i,k\) について

\[
P_{ik}+\sum_{j\ne i,k}P_{ij}P_{jk}=J_6.
\tag{3}
\]

ここで \(J_6\) は \(6\times6\) の全 1 行列である。

この式の意味は明確である。\(S_i\) の頂点と \(S_k\) の頂点の間には、

- 直接辺があるか、
- ある第三の fiber \(S_j\) を通る長さ 2 の道があるか、

のいずれかがちょうど 1 通りで起こる。したがって式 (3) に現れる 6 個の置換行列は、\(J_6\) の 1 の位置を重複なく分割する。

---

### 7.3 置換 \(P_{ij}\) は固定点なしの involution

まず、\(i,j\ge2\), \(i\ne j\) なら \(P_{ij}\) は固定点を持たない。もし \(P_{ij}(t)=t\) なら、

\[
(1,t),\ (i,t),\ (j,t)
\]

が三角形を作るからである。

次に、\(P_{ij}\) が involution であることを示す。ここが Hoffman–Singleton の一意性証明の本質的なスペクトル部分である。

\(\operatorname{srg}(50,7,0,1)\) の制限固有値は

\[
x^2+x-6=0
\]

の根、すなわち

\[
2, -3
\]

である。トレース条件からスペクトルは

\[
7^1, 2^{28}, (-3)^{21}
\]

となる。

任意の \(P=P_{ij}\) について、\(S_1\cup S_i\cup S_j\) 上の誘導部分の隣接行列は

\[
M(P)=
\begin{pmatrix}
0&I&I\\
I&0&P\\
I&P^{-1}&0
\end{pmatrix}
\]

である。Hoffman–Singleton の原証明の固有空間計算は、\(M(P)\) が固有値 2 を少なくとも 3 重に持つことを示す。

この条件が \(P\) に何を強制するかは、直接計算で見える。\(M(P)(x,y,z)=2(x,y,z)\) とすると、

\[
y+z=2x,
\]

\[
x+Pz=2y,
\]

\[
x+P^{-1}y=2z.
\]

消去すると、固有値 2 の重複度は \(P+P^{-1}\) の固有値 2 の重複度に等しい。置換 \(P\) の cycle decomposition を見ると、\(P+P^{-1}\) は各 cycle ごとに固有値 2 を 1 回ずつ持つ。したがって、\(M(P)\) における固有値 2 の重複度は \(P\) の cycle の個数に等しい。

よって \(P\) は少なくとも 3 個の cycle を持つ。一方、上で見たように \(P\) は固定点を持たない。6 点上の固定点なし置換が少なくとも 3 個の cycle を持つには、cycle 型が

\[
(2)(2)(2)
\]

であるしかない。したがって

\[
P_{ij}=P_{ij}^{-1}
\]

であり、\(P_{ij}\) は固定点なし involution、すなわち 3 個の互いに素な transposition の積である。

---

### 7.4 共役関係

\(i,j,k\ge2\) が相異なるとき、次が成り立つ。

\[
P_{ik}P_{ij}P_{ik}=P_{jk}.
\tag{4}
\]

これは式 (3) と、各 \(P_{ij}\) が固定点なし involution であることから従う。

概略は次の通りである。\(P_{ij}\) を

\[
P_{ij}=(ab)(cd)(ef)
\]

と書く。式 (3) による disjointness 条件から、\(P_{ik}\) は \(a,b\) を \((cd),(ef)\) の異なる transposition から来る点と結ばなければならない。ラベルを取り替えて

\[
P_{ik}=(ac)(be)(df)
\]

としてよい。このとき、\(P_{jk}\) は \(P_{ij}\), \(P_{ik}\), および \(P_{ij}P_{ik}\) と 1 の位置を共有してはいけない。可能な固定点なし involution は一意で、

\[
P_{jk}=(af)(bd)(ce)
\]

となる。直接掛け算すると式 (4) が得られる。

---

### 7.5 15 個の involution が全て現れる

\(2\le i<j\le7\) に対して \(P_{ij}\) は 15 個ある。一方、6 点集合上の固定点なし involution の個数は

\[
(6-1)!!=15
\]

である。

まず、これら 15 個の \(P_{ij}\) は互いに異なる。もし異なる pair に同じ involution が出るとする。添字を付け替えて

\[
P_{23}=P_{45}
\]

としてよい。共役関係 (4) を使うと

\[
P_{24}=P_{35},
\qquad
P_{25}=P_{34}
\]

が従う。すると、式 (3) の disjointness 条件を対応する行・列に適用して

\[
P_{26}+P_{27}=P_{36}+P_{37}=P_{46}+P_{47}
\]

となる。ここで各和は互いに素な 2 個の置換行列の和であるため、さらに

\[
P_{36}=P_{27},
\qquad
P_{46}=P_{27}
\]

が従う。しかしこれは同じ行または列の中で同じ置換行列が重複することを意味し、式 (3) に反する。

したがって 15 個の \(P_{ij}\) は相異なる。よって、6 点上の固定点なし involution 15 個が全てちょうど 1 回ずつ現れる。

---

### 7.6 標準形の決定

6 点集合を \(\{1,2,3,4,5,6\}\) とする。添字と fiber 内ラベルを取り替えて、次のように標準化できる。

\[
P_{23}=(12)(34)(56).
\]

式 (3) を \((i,k)=(1,2)\) に適用すると、

\[
I+P_{23}+P_{24}+P_{25}+P_{26}+P_{27}=J_6.
\]

したがって \(P_{23},P_{24},P_{25},P_{26},P_{27}\) は、\(K_6\) の 1-factorization を与える。さらにラベルを取り替えて、標準的に

\[
\begin{aligned}
P_{23}&=(12)(34)(56),\\
P_{24}&=(13)(25)(46),\\
P_{25}&=(14)(26)(35),\\
P_{26}&=(15)(24)(36),\\
P_{27}&=(16)(23)(45)
\end{aligned}
\tag{5}
\]

としてよい。

残りの \(P_{ij}\) は共役関係 (4) から一意に決まる。具体的には、\(3\le j<k\le7\) について

\[
P_{jk}=P_{2j}P_{2k}P_{2j}.
\tag{6}
\]

合成は右から左へ読む約束で、得られる標準表は次である。

| \(ij\) | \(P_{ij}\) |
|---:|---|
| 23 | \((12)(34)(56)\) |
| 24 | \((13)(25)(46)\) |
| 25 | \((14)(26)(35)\) |
| 26 | \((15)(24)(36)\) |
| 27 | \((16)(23)(45)\) |
| 34 | \((16)(24)(35)\) |
| 35 | \((15)(23)(46)\) |
| 36 | \((13)(26)(45)\) |
| 37 | \((14)(25)(36)\) |
| 45 | \((12)(36)(45)\) |
| 46 | \((14)(23)(56)\) |
| 47 | \((15)(26)(34)\) |
| 56 | \((16)(25)(34)\) |
| 57 | \((13)(24)(56)\) |
| 67 | \((12)(35)(46)\) |

これで全ての fiber 間マッチングが一意に決まった。したがって任意の \(\operatorname{srg}(50,7,0,1)\) はこの標準形に同型である。

最後に、この標準形は §5 の Robertson/biaffine 構成から得られる Hoffman–Singleton graph と一致する。よって \(\operatorname{srg}(50,7,0,1)\) は一意である。\(\square\)

---

## 8. Hoffman–Singleton graph の自己同型群

> **定理.** Hoffman–Singleton graph \(H\) の自己同型群は
> \[
> \operatorname{Aut}(H)\cong P\Sigma U_3(5)
> \cong PSU_3(5):2
> \]
> であり、位数は
> \[
> 252000
> \]
> である。頂点安定化群は \(S_7\) である。

### 8.1 下からの評価：\(P\Sigma U_3(5)\) の作用

Hoffman–Singleton graph には、\(P\Sigma U_3(5)\) の rank 3 作用がある。この作用の点安定化群は \(S_7\) であり、subdegree は

\[
1+7+42
\]

である。長さ 7 の軌道を隣接関係として取ると、次数 7、直径 2、girth 5 のグラフが得られる。一意性により、これは Hoffman–Singleton graph である。

したがって

\[
P\Sigma U_3(5)\le \operatorname{Aut}(H).
\]

位数は

\[
|P\Sigma U_3(5)|=2|PSU_3(5)|=252000.
\]

よって

\[
|\operatorname{Aut}(H)|\ge252000.
\]

同じ事実は biaffine 構成からも見える。点・直線への分割を保つ affine automorphism は 2000 個ある。Hoffman–Singleton graph にはそのような biaffine split が 126 個あり、全体として

\[
126\cdot 2000=252000
\]

個の自己同型が構成される。

---

### 8.2 上からの評価：頂点安定化群は高々 \(S_7\)

頂点 \(\infty\) を固定する自己同型群 \(G_\infty\) を考える。これは近傍集合

\[
N(\infty)=\{a_1,\dots,a_7\}
\]

に作用するので、準同型

\[
G_\infty\to S_7
\]

がある。この核が自明であることを示す。

核に属する自己同型 \(g\) は、\(\infty\) と全ての \(a_i\) を固定する。したがって各 fiber \(S_i\) を集合として保つ。\(S_i\) 上の作用を \(R_i\in S_6\) と書く。

標準化 \(P_{1j}=I\) のもとで、\(S_1\) と \(S_j\) の間のマッチングは identity である。これを保つためには

\[
R_j=R_1
\qquad(j=2,\dots,7)
\]

でなければならない。

さらに \(S_i\) と \(S_j\) の間のマッチング \(P_{ij}\) を保つので、全ての \(i,j\ge2\) について

\[
R_1P_{ij}=P_{ij}R_1
\]

である。ところが §7 で見たように、\(P_{ij}\) は 6 点集合上の全ての固定点なし involution を走る。固定点なし involution 全体は \(S_6\) を生成する。したがって \(R_1\) は \(S_6\) 全体と可換である。

\(S_6\) の中心は自明なので、\(R_1=I\)。よって全ての \(R_i=I\) であり、\(g\) は全頂点を固定する。核は自明である。

したがって

\[
G_\infty\hookrightarrow S_7,
\]

すなわち

\[
|G_\infty|\le7!.
\]

よって軌道安定化定理から

\[
|\operatorname{Aut}(H)|
\le 50\cdot 7!
=252000.
\]

一方で §8.1 により \(252000\) 個の自己同型が存在する。したがって

\[
|\operatorname{Aut}(H)|=252000.
\]

また頂点安定化群は実際に \(S_7\) 全体である。

---

### 8.3 群の同型型

位数 \(252000\) の自己同型群には、最大 coclique の 2 つの族をそれぞれ保つ index 2 部分群がある。この部分群の位数は

\[
126000
\]

であり、これは単純群

\[
PSU_3(5)
\]

と同型である。2 つの族を入れ替える外部 involution を加えると full group になる。したがって

\[
\operatorname{Aut}(H)
\cong PSU_3(5):2
\cong P\Sigma U_3(5).
\]

---

## 9. まとめ

Petersen graph と Hoffman–Singleton graph は、どちらも

\[
\operatorname{srg}(k^2+1,k,0,1)
\]

という同じ系列に属する。Petersen graph では fiber サイズが 2 なので、一意性は完全マッチングの交差・非交差だけで即座に決まる。

Hoffman–Singleton graph では fiber サイズが 6 になり、fiber 間マッチングは \(S_6\)-値のデータ

\[
P_{ij}\in S_6
\]

になる。強正則条件は

\[
P_{ik}+\sum_{j\ne i,k}P_{ij}P_{jk}=J_6
\]

という強い分解条件を与える。さらにスペクトル条件により、各 \(P_{ij}\) は固定点なし involution となる。固定点なし involution はちょうど 15 個あり、\(2\le i<j\le7\) の 15 個の block に全て 1 回ずつ現れる。この有限構造が標準形を強制し、一意性が得られる。

自己同型群については、Petersen graph では Kneser 表示 \(KG(5,2)\) から \(S_5\) が即座に現れ、最大独立集合を使ってそれ以上ないことを示せる。Hoffman–Singleton graph では、頂点安定化群が近傍 7 点への faithful action により \(S_7\) 以下であること、かつ \(P\Sigma U_3(5)\) の rank 3 作用が存在することから、

\[
\operatorname{Aut}(H)
\cong P\Sigma U_3(5)
\]

が決まる。

---

## 参考文献・出典

1. A. J. Hoffman and R. R. Singleton, **On Moore Graphs with Diameters 2 and 3**, IBM Journal of Research and Development 4 (1960), 497–504. 直径 2 の Moore graph について、次数 \(2,3,7\) の一意性と次数 \(57\) の未解決性を示す原論文。
2. W. H. Haemers, **Matrix techniques for strongly regular graphs and related geometries**, lecture notes, 2000. 強正則グラフの行列条件、Petersen graph の \((10,3,0,1)\) 表示、\((v,k,0,1)\) の可能パラメータを整理している。
3. A. E. Brouwer and H. Van Maldeghem, **Strongly Regular Graphs**, draft monograph. 小さい強正則グラフの列挙表に \((10,3,0,1)\) と \((50,7,0,1)\) の一意性が記載されている。
4. A. E. Brouwer, **Hoffman-Singleton graph**, online graph description. パラメータ、スペクトル、自己同型群 \(PSU(3,5).2\)、点安定化群 \(S_7\) を記載。
5. P. R. Hafner, **The Hoffman-Singleton Graph and its Automorphisms**, Journal of Algebraic Combinatorics 18 (2003), 7–12. Hoffman–Singleton graph の幾何的構成と自己同型群の構成。
6. P. R. Hafner, **On the Graphs of Hoffman-Singleton and Higman-Sims**, Electronic Journal of Combinatorics 11 (2004), #R77. Robertson の \(25+25\) 構成、biaffine plane 解釈、Hoffman–Singleton graph の自己同型群の位数と \(PSU(3,5)\) の同定に関する説明を含む。
7. L. O. James, **A combinatorial proof that the Moore (7,2) graph is unique**, Utilitas Mathematica 5 (1974), 79–84. Hoffman–Singleton graph の一意性に対する組合せ的証明。
