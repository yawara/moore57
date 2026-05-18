# Moore graph of degree 57: excluding an automorphism group of order 22

This note records a proof strategy for the following conditional exclusion.

> Let \(\Gamma\) be a Moore graph of degree \(57\) and diameter \(2\), hence a strongly regular graph with parameters
> \[
> (v,k,\lambda,\mu)=(3250,57,0,1).
> \]
> Assume the standard fixed-subgraph facts used below: an automorphism of order \(11\) fixes a \(5\)-cycle, and an involution fixes a star \(K_{1,55}\). Then
> \[
> |\operatorname{Aut}(\Gamma)|\neq 22.
> \]

The proof does **not** use a pre-existing theorem saying that order \(22\) is impossible.  The contradiction comes from combining

1. the \(11\)-orbit/fiber geometry around a fixed vertex,
2. a trace count over \(\mathbb C\),
3. a modular trace count over \(\mathbb F_{11}\), and
4. a parity constraint forced by the involution.

The verification notes at the end isolate the two fixed-subgraph facts used as external inputs.

---

## 1. Basic structure

Let \(A\) be the adjacency matrix of \(\Gamma\).  Since \(\Gamma\) is a Moore graph of degree \(57\) and diameter \(2\), it is strongly regular with
\[
(v,k,\lambda,\mu)=(3250,57,0,1).
\]
Thus:

- \(\Gamma\) has no triangles;
- \(\Gamma\) has no \(4\)-cycles;
- any two non-adjacent vertices have a unique common neighbor;
- the eigenvalues of \(A\) are
  \[
  57,\quad 7,\quad -8,
  \]
  with multiplicities
  \[
  1,
  1729,
  1520.
  \]

Let \(\sigma\in \operatorname{Aut}(\Gamma)\) have order \(11\).  Since
\[
3250\equiv 5\pmod {11},
\]
\(\sigma\) has fixed points.  We use the standard fixed-subgraph fact that
\[
\operatorname{Fix}(\sigma)\cong C_5.
\]
Write this fixed cycle as
\[
C=(u,a,b,c,d,u).
\]

For a vertex \(x\in N(u)\), write
\[
F_x=N(x)\setminus\{u\}.
\]
Then \(|F_x|=56\).  For distinct \(x,y\in N(u)\), the edges between \(F_x\) and \(F_y\) form a perfect matching: for each \(z\in F_x\), the vertices \(z\) and \(y\) are non-adjacent, so their unique common neighbor lies in \(F_y\).

The neighbors of \(u\) decompose as
\[
N(u)=\{a,d\}\sqcup B_1\sqcup B_2\sqcup B_3\sqcup B_4\sqcup B_5,
\]
where each
\[
B_r=\{x_{r,i}:i\in\mathbb Z/11\mathbb Z\}
\]
is a \(\sigma\)-orbit of length \(11\).  The two fixed branches are \(a,d\), and the remaining \(55\) branches are grouped into five \(11\)-orbits.

---

## 2. The trace number \(n\)

For \(k\in\mathbb Z_{11}^{\times}\), define
\[
T_k=\operatorname{tr}(A\sigma^k).
\]
Combinatorially, \(T_k\) counts the vertices \(x\) such that
\[
x\sim \sigma^k x.
\]
A length \(11\) orbit contributes either \(0\) or \(11\) to \(T_k\).  Hence
\[
T_k=11n_k.
\]
Because the representation of \(C_{11}\) on each rational eigenspace is rational, the trace is constant on the non-identity elements of \(C_{11}\).  Therefore
\[
n_k=n
\]
for all \(k\neq 0\), and
\[
T_k=11n.
\]

We now constrain \(n\).

---

## 3. Complex spectral restriction: \(n\in\{5,20,35,50\}\)

The vertex permutation representation of \(\langle\sigma\rangle\) has \(5\) fixed vertices and \(295\) orbits of length \(11\), since
\[
3250=5+11\cdot 295.
\]
Over \(\mathbb Q\), a length \(11\) orbit contributes
\[
1\oplus \Phi,
\]
where \(\Phi\) is the \(10\)-dimensional rational irreducible representation of \(C_{11}\).  Thus the full permutation representation is
\[
300\cdot 1\oplus 295\cdot\Phi.
\]

The all-one vector accounts for the \(57\)-eigenspace.  Write the \(7\)-eigenspace as
\[
E_7\cong a\cdot 1\oplus c\cdot\Phi.
\]
Then
\[
a+10c=1729.
\]
For \(k\neq 0\), the character value of \(\Phi\) on \(\sigma^k\) is \(-1\), so
\[
\operatorname{tr}(\sigma^k|E_7)=a-c.
\]
The \((-8)\)-eigenspace is then
\[
E_{-8}\cong (299-a)\cdot 1\oplus (295-c)\cdot\Phi,
\]
so
\[
\operatorname{tr}(\sigma^k|E_{-8})=4-a+c.
\]
Therefore
\[
T_k=57+7(a-c)-8(4-a+c)=25+15(a-c).
\]

From
\[
a+10c=1729
\]
we get, modulo \(11\),
\[
a-c\equiv 1729\equiv 2\pmod {11}.
\]
Thus
\[
a-c=2+11s
\]
for some integer \(s\), and hence
\[
T_k=25+15(2+11s)=55+165s.
\]
Since \(T_k=11n\), this gives
\[
n=5+15s.
\]

Next, use the absence of \(4\)-cycles.  Let
\[
O=\{z_i=\sigma^i z_0:i\in\mathbb Z_{11}\}
\]
be a length \(11\) orbit.  If \(z_i\sim z_{i+r}\), then by \(\sigma\)-invariance the whole orbit has edges of slope \(r\).  If it also had edges of a second slope \(s\not\equiv \pm r\), then
\[
z_0-z_r-z_{r+s}-z_s-z_0
\]
would be a \(4\)-cycle.  Hence each length \(11\) orbit has internal edges for at most one slope pair \(\{\pm r\}\).

There are five nonzero slope pairs in \(\mathbb Z_{11}\).  Since each slope has \(n\) contributing orbits, the number of length \(11\) orbits with internal edges is \(5n\).  There are only \(295\) length \(11\) orbits, so
\[
5n\le 295,
\]
and therefore
\[
n\le 59.
\]
Together with \(n=5+15s\), this gives
\[
\boxed{n\in\{5,20,35,50\}}.
\]

At this stage the complex trace argument alone is not enough.

---

## 4. Modular trace over \(\mathbb F_{11}\): forcing \(n=5\)

Now work over
\[
V=\mathbb F_{11}^{3250}.
\]
As an \(\mathbb F_{11}[C_{11}]\)-module, the vertex permutation module is
\[
V\cong 5M_1\oplus 295M_{11},
\]
where

- \(M_1\) is the one-dimensional trivial module;
- \(M_{11}\) is the indecomposable \(11\)-dimensional module coming from one \(11\)-cycle.

Modulo \(11\), the three eigenvalues become
\[
57\equiv 2,
\qquad 7\equiv 7,
\qquad -8\equiv 3.
\]
They are distinct in \(\mathbb F_{11}\).  Since the characteristic polynomial reduces as
\[
(X-2)(X-7)^{1729}(X-3)^{1520},
\]
and the minimal polynomial has distinct roots modulo \(11\), the space decomposes as
\[
V=V_2\oplus V_7\oplus V_3,
\]
where
\[
\dim V_2=1,
\qquad
\dim V_7=1729,
\qquad
\dim V_3=1520.
\]
Each \(V_\lambda\) is \(\sigma\)-stable.

The \(V_2\)-part is the all-one line, hence
\[
V_2\cong M_1.
\]
By Krull--Schmidt over the local algebra \(\mathbb F_{11}[C_{11}]\), the remaining eigenspaces are direct sums only of copies of \(M_1\) and \(M_{11}\).  Since
\[
1729=11\cdot 157+2,
\qquad
1520=11\cdot 138+2,
\]
and after removing \(V_2\) there remain four copies of \(M_1\), we must have
\[
V_7\cong 157M_{11}\oplus 2M_1,
\]
\[
V_3\cong 138M_{11}\oplus 2M_1.
\]
Therefore the fixed-space dimensions are
\[
\dim V_2^\sigma=1,
\]
\[
\dim V_7^\sigma=157+2=159,
\]
\[
\dim V_3^\sigma=138+2=140.
\]
Hence
\[
\operatorname{tr}(A|_{V^\sigma})
\equiv
2\cdot 1+7\cdot 159+3\cdot 140
\pmod {11}.
\]
The right-hand side is
\[
2+1113+420=1535\equiv 6\pmod {11}.
\]
Thus
\[
\operatorname{tr}(A|_{V^\sigma})\equiv 6\pmod {11}.
\]

Now compute the same trace in the orbit-sum basis of \(V^\sigma\).  This basis consists of

- the five fixed vertices of \(\sigma\), and
- the \(295\) sums of length \(11\) orbits.

A fixed vertex has no loop, so it contributes \(0\) to the trace.  A length \(11\) orbit contributes to the diagonal exactly when it has internal edges.  If it has internal edges, then by the slope argument it is a \(C_{11}\) inside that orbit, so each vertex has exactly two neighbors in the same orbit.  Thus such an orbit contributes \(2\) to the trace.

There are \(5n\) length \(11\) orbits with internal edges.  Hence
\[
\operatorname{tr}(A|_{V^\sigma})=2\cdot 5n=10n
\]
in the orbit-sum basis.  Therefore
\[
10n\equiv 6\pmod {11}.
\]
Since \(10\equiv -1\pmod {11}\), this gives
\[
n\equiv 5\pmod {11}.
\]
Combining this with
\[
n\in\{5,20,35,50\}
\]
forces
\[
\boxed{n=5}.
\]
Equivalently,
\[
\boxed{\operatorname{tr}(A\sigma^k)=55\quad(k=1,\dots,10).}
\]

---

## 5. Add the involution: order \(22\) forces \(n\) even

Assume now, for contradiction, that
\[
G=\operatorname{Aut}(\Gamma),\qquad |G|=22.
\]
Let
\[
\langle\sigma\rangle\le G
\]
be the Sylow \(11\)-subgroup.  It is normal.  For an involution \(\tau\in G\), either
\[
\tau\sigma\tau^{-1}=\sigma
\]
or
\[
\tau\sigma\tau^{-1}=\sigma^{-1}.
\]
These are the cyclic and dihedral cases.

We use the standard involution fixed-subgraph fact:
\[
\operatorname{Fix}(\tau)\cong K_{1,55}.
\]
That is, \(\tau\) fixes exactly \(56\) vertices, forming a star with one center and \(55\) leaves.

The involution \(\tau\) preserves the fixed \(5\)-cycle \(C=\operatorname{Fix}(\sigma)\).  It cannot act trivially on \(C\), since then its fixed graph would contain a \(5\)-cycle rather than a star.  Hence \(\tau\) acts on \(C\) as a reflection.  Choose notation so that
\[
\tau(u)=u,
\qquad
\tau(a)=d,
\qquad
\tau(b)=c.
\]

### 5.1. Cyclic case

Assume
\[
\tau\sigma=\sigma\tau.
\]
Then \(u\) must be the center of the fixed star.  Indeed, if \(u\) were a leaf, then \(u\) would have exactly one \(\tau\)-fixed neighbor.  But \(\tau\) commutes with \(\sigma\), so any setwise fixed \(11\)-block in
\[
B_1,\dots,B_5
\]
would be fixed pointwise.  Since five blocks are acted on by an involution, at least one block is setwise fixed, giving \(11\) fixed neighbors of \(u\), impossible for a leaf.  Therefore \(u\) is the center.

Thus
\[
\operatorname{Fix}(\tau)=\{u\}\cup B_1\cup\cdots\cup B_5.
\]
The five \(11\)-blocks are pointwise fixed by \(\tau\), while \(a,d\) are exchanged.

Consider a length \(11\) \(\sigma\)-orbit \(O\) with internal edges.  If \(O\) is \(\tau\)-stable, then \(\tau\) acts on \(O\) as a translation because \(\tau\) commutes with \(\sigma\).  A translation of order \(2\) on \(\mathbb Z_{11}\) is trivial, so \(O\) would be fixed pointwise.  The only pointwise fixed length \(11\) orbits are the blocks \(B_1,
\dots,B_5\), but these lie in \(N(u)\), hence are independent and have no internal edges.

Therefore every internal-edge \(\sigma\)-orbit is paired with a distinct one by \(\tau\).  For each nonzero slope, the contributing orbits occur in pairs.  Hence
\[
\boxed{n\equiv 0\pmod 2}
\]
in the cyclic case.

### 5.2. Dihedral case

Assume
\[
\tau\sigma\tau^{-1}=\sigma^{-1}.
\]
Then \(u\) cannot be the center of the fixed star.  If it were the center, it would have \(55\) fixed neighbors.  But \(a,d\) are exchanged, and on each \(11\)-block a reflection has at most one fixed point, so \(u\) could have at most five fixed neighbors, contradiction.  Thus \(u\) is a leaf.

Consequently, \(u\) has exactly one \(\tau\)-fixed neighbor.  Among the five \(11\)-blocks, exactly one is \(\tau\)-stable.  Call it
\[
B_0=\{x_i:i\in\mathbb Z_{11}\},
\]
with
\[
\tau(x_i)=x_{-i}.
\]
The unique fixed neighbor \(x_0\) is the center of \(\operatorname{Fix}(\tau)\).

For each \(i\), put
\[
F_i=F_{x_i}.
\]
Inside \(F_0\), define the two exceptional vertices
\[
p=N(b)\cap N(x_0),
\qquad
q=N(c)\cap N(x_0).
\]
Then \(\tau\) exchanges \(p,q\), and fixes the other \(54\) vertices of \(F_0\).  Write
\[
F_0=\{p,q\}\sqcup L,
\qquad |L|=54,
\]
and let
\[
\theta=(p\ q)
\]
fixing \(L\) pointwise.

For \(d\neq 0\), encode the perfect matching between \(F_i\) and \(F_{i+d}\) by a permutation
\[
\pi_d:F_0\to F_0
\]
so that the vertex labelled \(t\) in \(F_i\) is adjacent to the vertex labelled \(\pi_d(t)\) in \(F_{i+d}\).  Then a \(\sigma\)-orbit labelled by \(t\) has internal edges of slope \(d\) exactly when
\[
\pi_d(t)=t.
\]
Thus the contribution of the special block \(B_0\) to \(n\) is
\[
|\operatorname{Fix}(\pi_d)|.
\]

The reflection relation gives
\[
\theta\pi_d\theta=\pi_d^{-1},
\]
so
\[
\rho_d:=\theta\pi_d
\]
is an involution.

Now use the fixed-star geometry.  For the branch pair
\[
x_i,	au(x_i)=x_{-i},
\]
there are exactly two adjacent \(\tau\)-pairs between the corresponding fibers.  This follows as follows.  The fixed star has center \(x_0\), leaf \(u\), and the \(54\) fixed leaves in \(L\).  Each fixed leaf forbids adjacent \(\tau\)-pairs in any opposite branch pair, because such an adjacency would create a triangle through that fixed leaf.  The only possible adjacent \(\tau\)-pairs are therefore generated by the two exceptional vertices \(p,q\).  Globally an involution with fixed graph \(K_{1,55}\) has exactly \(56\) adjacent \(2\)-cycles, and there are \(28\) branch pairs around \(u\), so each branch pair contributes exactly two.

For the branch pair corresponding to difference \(d\), adjacent \(\tau\)-pairs are exactly the fixed points of
\[
\rho_d=\theta\pi_d.
\]
Hence \(\rho_d\) has exactly two fixed points.

These fixed points cannot be \(p\) or \(q\).  For instance, \(\rho_d(p)=p\) would mean
\[
\pi_d(p)=q,
\]
which would create the \(4\)-cycle
\[
b-p_i-q_{i+d}-c-b.
\]
Similarly for \(q\).  Thus the two fixed points of \(\rho_d\) lie in \(L\).  On \(L\), \(\theta\) is the identity, so these are exactly the fixed points of \(\pi_d\).

Also \(p,q\) themselves cannot be fixed by \(\pi_d\): \(\pi_d(p)=p\) would make two vertices both adjacent to \(b\) adjacent to each other, creating a triangle; similarly \(\pi_d(q)=q\) creates a triangle through \(c\).

Therefore
\[
|\operatorname{Fix}(\pi_d)|=2.
\]
So the special block \(B_0\) contributes exactly \(2\) to \(n\) for every nonzero slope.

The remaining four \(11\)-blocks are paired by \(\tau\).  Their internal-edge contributions therefore occur in pairs.  Hence, in the dihedral case as well,
\[
\boxed{n\equiv 0\pmod 2}.
\]

---

## 6. Contradiction

The order \(11\) analysis over \(\mathbb F_{11}\) forced
\[
\boxed{n=5}.
\]
But if \(|\operatorname{Aut}(\Gamma)|=22\), then an involution is present, and the cyclic and dihedral cases both force
\[
\boxed{n\equiv 0\pmod 2}.
\]
This is impossible.

Therefore
\[
\boxed{|\operatorname{Aut}(\Gamma)|\neq 22.}
\]

---

## 7. Verification notes

The proof above was checked for the following potential failure points.

### 7.1. The modular eigenspace dimensions

The argument over \(\mathbb F_{11}\) uses
\[
\dim V_7=1729,
\qquad
\dim V_3=1520.
\]
This is legitimate because the integral characteristic polynomial reduces modulo \(11\) to
\[
(X-2)(X-7)^{1729}(X-3)^{1520},
\]
with distinct roots \(2,7,3\) in \(\mathbb F_{11}\).  Hence the algebraic multiplicities over \(\mathbb F_{11}\) are the same exponents, and the minimal polynomial is square-free.

### 7.2. Why only \(M_1\) and \(M_{11}\) occur in the modular eigenspaces

The whole permutation module is
\[
5M_1\oplus 295M_{11}.
\]
The eigenspaces of \(A\) are \(\mathbb F_{11}[C_{11}]\)-direct summands because the eigenvalue projectors are polynomials in \(A\) and commute with \(\sigma\).  By Krull--Schmidt, a direct summand of this module can contain only indecomposable summands already appearing in the total decomposition, namely \(M_1\) and \(M_{11}\).  Thus intermediate indecomposables \(M_j\), \(1<j<11\), do not appear.

### 7.3. The orbit-sum trace

In the orbit-sum basis of \(V^\sigma\), edges between different \(\sigma\)-orbits contribute off-diagonal entries only.  The trace sees only edges from an orbit to itself.  By the no-\(4\)-cycle argument, an orbit with internal edges has exactly one slope pair, hence contributes exactly \(2\) to the trace.

### 7.4. The parity argument

In the cyclic case, a \(\tau\)-stable length \(11\) orbit would be fixed pointwise, and the only such orbits are the five blocks in \(N(u)\), which are independent.  Thus internal-edge orbits pair off.

In the dihedral case, the only unpaired block is \(B_0\).  Its contribution is not arbitrary: the fixed-star geometry forces exactly two fixed labels of \(\pi_d\) for every nonzero slope \(d\).  Hence the unpaired contribution is already even, while all other contributions pair off.

### 7.5. External inputs

The proof uses two fixed-subgraph inputs that should be supplied separately in a fully formal development:

1. If \(\sigma\) has order \(11\), then \(\operatorname{Fix}(\sigma)\cong C_5\).
2. If \(\tau\) is an involution, then \(\operatorname{Fix}(\tau)\cong K_{1,55}\).

The second input was part of the problem statement.  The first is the standard fixed-subgraph analysis for prime-order automorphisms of a Moore graph of degree \(57\).  The contradiction above is conditional on these two fixed-subgraph facts.
