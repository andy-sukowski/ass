#import "@preview/fletcher:0.5.8": *
#import "@preview/wrap-it:0.1.1": *
#import "@preview/xarrow:0.3.1": xarrow

#import "thm.typ": *
#show: great-theorems-init

#set document(
  title: "Cohomology, Steenrod Algebra, and the Adams Spectral Sequence",
  author: ("Alex Herbst", "Andy Sukowski-Bang", "Emma Howe"),
)
#set heading(numbering: "1.1")
#set page(
  numbering: "1 of 1",
  header: context {
    if counter(page).get().first() > 1 [
      #show: smallcaps
      Adams Spectral Sequence
      #h(1fr)
      Christian-Albrechts-Universität
    ]
  },
)
#set text(font: "New Computer Modern")
#set par(justify: true)

#show heading: smallcaps
#show heading: set text(weight: "regular")
#show heading: set par(justify: false)
#show heading: set block(above: 2em, below: 1em)
#show link: text.with(fill: blue)
#show sym.colon: math.class("fence", sym.colon)

#let definition  = fancy_mathblock(blocktitle: "Definition")
#let theorem     = fancy_mathblock(blocktitle: "Theorem")
#let lemma       = fancy_mathblock(blocktitle: "Lemma")
#let proposition = fancy_mathblock(blocktitle: "Proposition")
#let corollary   = fancy_mathblock(blocktitle: "Corollary")
#let example     = plain_mathblock(blocktitle: "Example")
#let proof       = proofblock()

#let cup     = math.op("⌣")
#let colim   = math.op("colim")
#let dirlim  = $limits(display(lim_(#pad(top: -0.9em, bottom: -0.3em, math.stretch(math.arrow, size: 1.1em)))))$
#let Ext     = math.op("Ext")
#let Hom     = math.op("Hom")
#let Sq      = math.op(math.italic("Sq"))
#let Top     = $bold("Top"_*)$
#let LMod(r) = $#(r)bold("-Mod")$
#let Ab      = $bold("Ab")$

#let col(color, x) = text(fill: color)[$#x$]

#align(center, context [
  #set par(justify: false)
  #text(size: 20pt, smallcaps(document.title))

  #document.author.join(h(3em))
  #v(2em)
])

#outline()

= Cohomology and the Ext-Functor

== $Ext_R (A,B)$ and projective resolutions

Let $R$ be a ring and denote by $LMod(R)$ the category of left R-modules.

#definition(title: [(Cochain Complex and Cohomology Module) @homalg[p. 118]])[
  A cochain complex is a family ${C_n}_(n in ZZ), C_n in LMod(R)$ and ${delta_n}_(n in ZZ), delta_n in Hom_R (C_(n-1),C_n)$ such that $delta_n delta_(n-1)=0$. We call $H(C):={H^n (C)}_(n in ZZ)$ the cohomology module where 
  $
    H^n (C):= (ker delta_n) / (im delta_(n-1))
  $
  is the n-th cohomology module.
]

In order to define right derived functors we need projective resolutions.

#definition(title: [(Projective Resolution)])[
  A projective resolution $P$ of $M in LMod(R)$ is an exact sequence 
  $
    P: dots.c ->
    P_n ->
    P_(n-1) ->
    dots.c ->
    P_0 ->
    M ->
    0
  $
  where all $P_i$ are projective, that is for all $epsilon: B ->> C, gamma: P_i ->C$ exists $beta: P_i -> B$ such that $epsilon beta = gamma$.
]

Free resolutions are also projective resolutions since free modules are also projective by the universal properties. 

#lemma(title: [@homalg[Chapter IV. Lemma 4.2]])[
  To every $A in LMod(R)$ there exists a projective resolution.
]

The preceding result gives rise to the latter definition of right derived functors. First we have a few results that will be of use later.

#theorem(title: [@homalg[Chapter IV. Theorem 4.1]])[
  Let $C,D$ be projective resolutions of $A,B in LMod(R)$ and $phi: A -> B in Hom_R (A,B)$. Then a chain map $tilde(phi): C ->D$ exists that induces $phi$. Each two of such chain maps are homotopic.
]<thm4.1>

#proposition(title: [@homalg[Chapter IV. Corollary 3.5]])[
  For chain maps $phi tilde.eq psi: C-> D$ and an additive functor $F$ we have
  $
    H(F phi)=H(F psi): H(C)-> H(D).
  $
]<corollary3.5>

We are now ready to define the right drived functors and show that they are in fact functors.

#definition(title: [(Right Derived Functor) @homalg[p. 134]])[
  Let $S: LMod(R)-> Ab$ be an additive contravariant functor. We define the right derived functor $R^n S: LMod(R)-> Ab$ of $S$ on objects as
  $
    R^n S(A):= H^n (S P) 
  $
  where  
  $
    S P: dots.c -> S P_n -> S P_(n-1) -> dots.c -> S P_0 -> 0
  $

  for a projective resolution $P "of" A$. For $alpha in Hom_R (A,A'), A,A' in LMod(R)$ and $P,P'$ projective resolutions of $A,A'$ there exists a chain map $tilde(alpha): P-> P'$ by @thm4.1 that induces $alpha$. Applying $R^n S$ yields a map $R^n S(alpha): R^n S(A)-> R^n S(A')$ independent of $tilde(alpha)$ by @corollary3.5.
]<rdevfunc>

#theorem(title: [@homalg[p.131 (adapted)]])[
  $R^n S$ as in @rdevfunc is a functor.
] 

#proof()[
  Let $alpha in Hom_R (A,A'), alpha' in Hom_R (A',A'')$ and $P,P',P''$ be projective resolutions of $A,A',A''$. Then both $tilde(alpha)compose tilde(alpha')$ as well as $tilde(alpha compose alpha')$ are chain maps that induce $alpha compose alpha'$ and therefore homotopic by @thm4.1. @corollary3.5 yields that $R^n S(alpha compose alpha')=R^n S(alpha) compose R^n S(alpha')$. We also have that $R^n S(id_A)=id_(R^n S(A))$. This concludes the proof.
]

The reader might be inclined to think that one should write $R_P ^n S(A)$ instead of $R^n S(A)$ since the definition depends on the projective resolution $P$ of $A$. The following theorem shows the independence of the choice of projective resolution.

#proposition(title: [@homalg[Chapter IV. Proposition 5.1(adapted)]])[
  Let $P,Q$ be two projective resolutions of $A in LMod(R)$, then 
  $
  R_P ^n S(A) tilde.equiv R_Q ^n S(A).
  $
]

Since $Hom_R (-,B)$ is additive we are now ready to define $Ext_R ^n$ as the right derived functor of the Hom-functor.

#definition(title: [($Ext$-functor) @homalg[p. 139]])[
  For a ring $S$ and $B in LMod(S)$ we define 
  $
  Ext_S ^n (-,B):= R^n Hom_S (-,B).
  $
]

Since we will later want to use this definition for the calculation of cohomology groups the next few properties of Ext will come in handy.

#proposition(title: [@homalg[Chapter IV. Proposition 5.2, 5.3, 5.4]])[
  #set enum(numbering: "a)")
  + $Ext_R ^0 (-,B) tilde.equiv Hom_R (-,B)$.
  + $Ext_R ^n (A,B)=0$ for $n=1, 2, dots$ and $A$ projective.
  + $Ext_R ^n (A plus.circle A',B)= Ext_R ^n (A,B) plus.circle Ext_R ^n (A',B)$ 
  + $Ext_ZZ ^1(ZZ_n,G)=G slash n G$ for a group $G$
]<ext_properties>

#proof()[
  #set enum(numbering: "a)")
  + Let $A in LMod(R)$ and $P$ be a projective resolution of $A$. Then 
    $
      P_1 -> P_0 -> A -> 0
    $
    is exact and since $Hom_R (-,B)$ left exact and contravariant 
    $
      0 -> Hom_R (A,B) xarrow(phi) Hom_R (P_0,B) xarrow(psi) Hom_R (P_1,B)
    $
    exact. Therefore we get 
    $
      Ext_R ^0 (A,B):= H^0(Hom_R (P,B))= (ker psi)/(im 0)=im phi= (im phi)/(ker phi) tilde.equiv Hom_R (A,B).
    $
    This is implied by the first isomorphism theorem.
  + $
      P: dots.c -> 0 -> A -> A -> 0 
    $
    is a projective resolution for $A$. For $Hom_R (P,B)$ we have 
    $
      0 -> Hom_R (A,B) -> 0 -> 0 -> dots.c
    $
    and therefore 
    $
      Ext_R ^n (A,B)= H^n (Hom_R (P,B))= 0/0=0
    $
    for $n=1, 2, dots.c$.
  + Let $P,P'$ be projective resolutions of $A,A' in LMod(R)$, then $P plus.circle  P'$ is a projective resolution for $A plus.circle A'$. Since $Hom_R (-,B)$ is      additive the result follows.
  + A free resolution and therefore also a projective one for $ZZ_n$ is
    $
      P: 0 -> ZZ xarrow(n) ZZ -> ZZ_n -> 0.
    $
    Dualizing with $Hom(-,G)$ yields
    $
      Hom(P,G): 0->Hom(ZZ,G)tilde.equiv G xarrow(n^*=n) Hom(ZZ,G)tilde.equiv G->0
    $
    and $Ext_ZZ ^1(ZZ_n,G)=H^1(Hom(P,G))=Hom(ZZ,G) slash ker n^*= G slash n G$.
]

== Singular Cohomology for Spaces

Let $X$ be a topological space. From homology theory we know that
$
  C: dots.c -> C_(n+1) (X) xarrow(diff_(n+1)) C_n (X) xarrow(diff_n) C_(n-1) (X) -> dots.c
$
is a chain complex where $C_n (X)$ denotes the singular chain group and $diff_n$ boundary maps.
We can apply $Hom (-,G)$ for $G in Ab$ and get a cochain complex
$
  C^*: dots.c -> C^(n-1) (X;G) xarrow(delta_n) C^n (X;G) xarrow(delta_(n+1)) C^(n+1) (X;G) -> dots.c
$
where $C^n (X;G):=Hom (C_n (X),G)$ are the singular cochain groups and $delta_n:= diff_n ^*$ are the coboundary maps defined by $delta(alpha)= diff^*(alpha)= alpha compose diff$ for some map $alpha$.
This is in fact a cochain complex since
$
  delta_n delta_(n-1) (alpha)=diff_n ^* diff_(n-1) ^* (alpha)=diff_n ^* (alpha compose diff_(n-1))=alpha compose diff_(n-1) compose diff_n = alpha compose 0 = 0.
$
follows from the fact that $C$ is a chain complex.

#definition(title: [(Singular Cohomology for a Space) @at[p. 197]])[
  For the above construction we define the (singular) cohomology group of a topological space $X$ as 
  $
    H^n (X;G):= H^n (C^*)=(ker delta_n)/(im delta_(n-1)). 
  $
]

We will sometimes also write $H^n (C;G)$ for some chain complex $C$ and mean $H^n (Hom (C,G))$ by that.

For a pair $(X,A)$ of spaces we have
$
  0-> C_n (A) xarrow(i) C_n (X) xarrow(j) C_n (X,A) -> 0
$
exact. Here $i$ denotes the inclusion, $j$ the quotient map since $C_n (X,A):= C_n (X) slash C_n (A)$. Since $Hom (-,G)$ is left exact we get an exact sequence
$
  0-> C^n (X,A;G) xarrow(j^*) C^n (X;G) xarrow(i^*) C^n (A;G) -> 0
$
where $C^n (X,A;G):=Hom (C_n (X,A), G)$ by showing that $im j^* = ker i^*$ and $im i^*=C^n (A;G)$.
One gets relative cochain maps $delta_n ^A:C^n (X,A;G)-> C^(n+1) (X,A;G)$ by restricting the absolute cochain maps $delta_n: C^n (X;G)-> C^(n+1) (X;G)$ to 
$
  ker i^*:= {psi: C_n (X) -> G | psi(sigma)=0 "for all" sigma in C_n (A)}
$
which corresponds to $C^n (X,A;G)$. We can therefore define the following.

#definition(title: [(Relative Cohomology) @at[p. 199]])[
  For the above $delta_i ^A$ we define
  $
    H^n (X,A;G):= (ker delta_n ^A)/(im delta_(n-1) ^A)
  $
  to be the n-th relative cohomology group of the pair $(X,A)$.
]

Choosing $A$ as a point we get reduced cohomology.

#definition(title: [(Reduced Cohomology) @at[p. 200]])[
  $tilde(H)^n (X):=H^n (X,*;G)$
]

#proposition(title: [(Homotopy Invariance of Induced Homomorphisms on Cohomology) @at[p. 201]])[
  For $f tilde.eq g: (X,A)->(Y,B)$ we have $f^* = g^*: H^n (X,A;M)-> H^n (Y,B;M)$.
]

== The Universal Coefficient Theorem

We restrict ourselves to $ZZ$-modules i.e. abelian groups for the next statements. 

For $[phi] in H^n (C;G)$ we have $phi: C_n -> G$ as well as $phi in ker delta_(n+1)$. This yields that
$
  0=delta_(n+1) (phi)=phi compose diff_(n+1) <=> phi(im diff_(n+1))=0. 
$
We therefore get that $phi|_(ker diff_n)$ induces $tilde(phi_0): (ker diff_n)/(im diff_(n+1))=H_n(C)->G$. Now define a map
$
  h: H^n (C;G)-> Hom(H_n (C), G), h([phi]):=tilde(phi_0).
$

We get the following result known as the universal coefficient theorem.

#theorem(title: [(Universal Coefficient Theorem) @at[Theorem 3.2]])[
  $
    0 -> Ext_ZZ ^1(H_(n-1)(C),G) -> H^n (C;G) -> Hom(H_n (C),G) -> 0
  $
  is split exact.
] <uct>

There are more general results replacing abelian groups with $R$-modules for some ring $R$ and $Hom$ with $Hom_R$. One gets a split exact sequence
$
  0 -> Ext_R ^1(H_(n-1)(C),A) -> H^n (C;A) -> Hom_R(H_n (C),A) -> 0
$
where $A in LMod(R)$.

#example(title: "(Cohomology of Spheres)")[
  Remember that
  $
    H_n S^m =
    cases(
      ZZ\, &" if" n in {0,m},
      0\,  &" otherwise".
    )
  $
  Note that both $ZZ$ and $0$ are free and therefore also projective.
  Thus by @uct and @ext_properties:
  $
    H^n (S^m;G)
    tilde.equiv Ext(H_(n-1)(S^m),G) plus.circle Hom(H_n (S^m),G)
    tilde.equiv 0 plus.circle
    cases(
      G\, &" if" n in {0,m},
      0\, &" otherwise"
    )
  $
] <sphere_cohomology>

== Cup product

#definition(title: [(Cup Product for Cochains) @at[p. 206]])[
  Let $X$ be a topological space and $R$ be a ring.
  $
    cup: C^k (X;R) times C^ell (X;R) -> C^(k+ell)(X;R), phi cup psi (sigma):= phi(sigma|_([v_0,dots, v_k]))psi(sigma|_([v_k, dots, v_(k+ell)]))
  $
  for $sigma: Delta^(k+ell)-> X$ is called the cup product. This product is associative as well as distributive.
]

The following theorem is a tool to proof that the cup product descents to cohomology.

#lemma(title: [@at[Lemma 3.6]])[
  $
    delta_(k+ell+1) (phi cup psi)= delta_(k+1) phi cup psi + (-1)^k phi cup delta_(ell+1) psi.
  $
]

The cup product induces a product on the cohomology groups
$
  cup: H^k (X;R) times H^ell (X;R) -> H^(k+ell) (X;R)
$
since the product of two cocycles is again a cocycle and the product of a cocycle and a coboundary in either order is a coboundary. Since it was associative and distributive on the level of cochains we also get this for the cohomology groups. The neutral element is $[1]in H^0(X;R), 1: C_0 (X)-> R, 1(sigma):=1$.

#proposition(title: [@at[Proposition 3.10]])[
  For $R$ commutative we have
  $
    alpha cup beta = (-1)^(k dot l)beta cup alpha.
  $
]

#definition(title: [(Graded Cohomology Ring) @at[p. 212]])[
  For $[a],[b] in H^n (X;R)$ we have $a,b: C_n -> R$.
  Define $[a] + [b] := [a + b] in H^n (X;R)$.
  $
    H^*(X;R) := plus.big_(n>=0) H^n (X;R)
  $
  defines a _graded ring_ with the above addition and
  $(sum alpha_i) cup (sum beta_j) := sum_{i,j} alpha_i cup beta_j$
  as multiplication.
]

The cup product can also be defined for relative cohomology via
$
  H^k (X,A;R) times H^ell (X,B;R)xarrow(cup) H^(k+ell) (X,A union B;R)
$
if $A,B$ are open subsets of $X$ or subcomplexes of the CW complex $X$.

== The Cross Product and Suspension Isomorphism

We can define a cross product for the cohomology ring.

#definition(title: [(Cross Product) @at[p. 215]])[
  Let $p_1: X times Y ->> X$ and $p_2: X times Y ->> Y$ be the canonical projections.
  $
    times:
    H^* (X;R) times.circle_R H^* (Y;R) &-> H^* (X times Y;R), \
    x times.circle y                   &|-> p_1 ^* (x) cup p_2 ^* (y)
  $
  defines the _cross product_.
]

This is a ring homomorphism if we define $(a times.circle b)(c times.circle d):= (-1)^(|b||c|) a c times.circle b d$.

#definition(title: [(Relative Cross Product) @at[p.215]])[
  Let $p_1: X times Y ->> X$ and $p_2: X times Y ->> Y$ be the canonical projections.
  $
    times:
    H^*(X,A;R) times.circle_R H^*(Y,G;R)
    &-> H^*(X times Y, A times Y union X times B;R), \
    x times.circle y &|-> p_1^*(x) cup p_2^*(y)
  $
  defines the _relative cross product_.
] <relative_cross_product>

#definition(title: [(Smash Product) @cat[Definition 1.28]])[
  Let $or$ denote the wedge sum.
  By slight abuse of notation
  $
    X and Y
    := (X times Y)/(X times {y_0} union {x_0} times Y)
    = (X times Y)/(X or Y).
  $
] <smash_product>

#grid(
  columns: (auto,auto),
  gutter: 1em,
  align: horizon,
  definition(title: [(Reduced Suspension) @at[Example 0.10]])[
    The _suspension_ of $X$ is $S X := X times I slash ~$,
    where $(x,0) ~ (y,0)$ and $(x,1) ~ (y,1)$.
    Now let $X$ be a CW-complex and $x_0 in X$ a 0-cell.
    The _reduced suspension_ is $Sigma X := (S X)/({x_0} times I)$.
  ],
  figure(
    image("images/suspension.svg", width: 3em),
    caption: [$X := S^1$],
  )
)

#example[
  $X and S^k = Sigma^k X$.
] <smash_product_reduced_suspension>

#example(title: "(Reduced Cross Product)")[
  For $(X,{x_0})$ and $(Y,{y_0})$ we get a reduced cross product
  $
    tilde(H)^*(X;R) times.circle_R tilde(H)^*(Y;R) xarrow(times) tilde(H)^*(X and Y;R),
  $
  where $X and Y$ is the smash product from @smash_product.
] <reduced_cross_product>

#theorem(title: [(Künneth formula) @at[Theorem 3.18]])[
  For CW pairs $(X,A)$ and $(Y,G)$ the relative cross product in @relative_cross_product is an isomorphism of rings
  if for all $k$, $H^k (Y,G;R)$ is a finitely generated free $R$-module.
]

#corollary(title: "(Suspension Isomorphism)")[
  Let $r$ be a generator of $H^k (S^k;R) tilde.equiv R$, see @sphere_cohomology.
  With @smash_product_reduced_suspension and @reduced_cross_product in mind we get the _suspension isomorphism_
  $
    tilde(H)^n (X;R) xarrow(tilde.equiv) tilde(H)^(n+k) (Sigma^k X;R), quad
    x |-> times(x times.circle r).
  $
] <suspension_isomorphism>

= Steenrod Operations and the Steenrod Algebra

#grid(
  columns: (auto,auto),
  gutter: 1.5em,
  align: horizon,
  definition(title: [(Cohomology Operation) @at[p. 488]])[
    A _cohomology operation_ of type $(m,n,G,H)$ is a natural transformation
    $
      Theta: H^m (-;G) => H^n (-;H).
    $
  ],
  diagram(
    $
      H^m (Y;G) & H^n (Y;H) \
      H^m (X;G) & H^n (X;H)
    $,
    edge((0,0), "r", "->", $Theta_Y$, left),
    edge((0,0), "d", "->", $f^*$),
    edge((0,1), "r", "->", $Theta_X$),
    edge((1,0), "d", "->", $f^*$, left)
  )
)

#example[
  Cup product squaring yields a family of cohomology operations
  $
    Theta_X: H^m (X;G) &-> H^(2m)(X;G) \
    alpha              &|-> alpha cup alpha.
  $
]

#theorem(title: [(Properties of Steenrod Squares) @at[p. 489]])[
  $Sq^i: H^n (X;ZZ_2) -> H^(n+i) (X;ZZ_2)$ will satisfy

  #set enum(numbering: "(1)")
  + Naturality.
    $Sq^i (f^*(alpha)) = f^*(Sq^i (alpha))$ for $f: X -> Y$.

  + $Sq^i (alpha + beta) = Sq^i (alpha) + Sq^i (beta)$.

  + Cartan formula.
    $Sq^i (alpha cup beta) = sum_j Sq^j (alpha) cup Sq^(i-j) (beta)$

  + $Sq^i$'s are stable.
    $Sq^i (sigma(alpha)) = sigma(Sq^i (alpha))$
    where $sigma: H^n (X;ZZ_2) -> H^(n+1)(Sigma X;ZZ_2)$ is the suspension isomorphism from @suspension_isomorphism.

  + Steenrod squares extend $alpha |-> alpha^2$.
    $Sq^i (alpha) = alpha^2$ if $i = |alpha|$,
    and $Sq^i (alpha) = 0$ if $i > |alpha|$.

  + $Sq^0 = id$, the identity.

  + $Sq^1$ is the $ZZ_2$ Bockstein homomorphism $beta$ associated with the coefficient sequence
     $0 -> ZZ_2 -> ZZ_4 -> ZZ_2 -> 0$.
] <steenrod_squares_properties>

#theorem(title: [(Adem relation for $Sq$) @at[p. 496]])[
  $
    Sq^a Sq^b
    = sum_j binom(b-j-1,a-2j) Sq^(a+b-j) Sq^j,
    " if " a < 2b
  $
]

#definition(title: [(Steenrod Algebra $cal(A)_2$) @at[p. 496]])[
  $
    cal(A)_2 :=
    (ZZ_2 angle.l Sq^1, Sq^2, dots angle.r)/"(Adem relation)"
  $
]

#definition(title: [(Admissible Sequence) @op[Definition 3.3]])[
  Let $r$ be the _length_ of a sequence $I := {i_1, ..., i_r}$.
  $I$ is _admissible_ if $i_j >= 2 i_(j+1)$ for all $j < r$.
  Let $Sq^I := Sq^(i_1) dots.c Sq^(i_r)$ and $Sq^{} := Sq^0 = id$.
]

#theorem(title: [(Serre-Cartan Basis) @op[Theorem 6.2.1]])[
  The monomials $Sq^I$, as $I$ runs through all admissible sequences, form a basis for $cal(A)$ as a $ZZ_2$-module.
]

= The Adams Spectral Sequence and Low-Dimensional Computations

#figure(
  image("images/spectral_sequence_pages.svg", width: 100%),
  caption: [Pages of a spectral sequence and their differentials. @ss[p. 520]],
)

== Exact Couples

#definition(title: [(Filtration) @ss[p. 522]])[
  A sequence of subspaces
  $dots.c subset.eq X_s subset.eq X_(s+1) subset.eq dots.c$
  is a _filtration_ of $X := product.co X_s$.
]

By @at[Theorem 2.16] each pair $(X_s,X_(s-1))$ yields a _long exact sequence of homology_ with connecting homomorphisms $k$.
#math.equation(block: true, numbering: "(1)",
  $dots.c xarrow(k) H_n (X_(s-1)) xarrow(i) H_n (X_s) xarrow(j) H_n (X_s, X_(s-1)) xarrow(k) H_(n-1) (X_(s-1)) xarrow(i) dots.c$
) <long_exact_homology>
Considering all pairs $(X_s,X_(s-1))$ at once, we can interlock these long exact sequences in a _staircase diagram_:
#figure(
  diagram(
    spacing: (0.8em, 1em),
    $
      col(#red,H_(n+1)(X_s)) & col(#red,H_(n+1)(X_s,X_(s-1))) & col(#red,H_n (X_(s-1))) & H_n (X_(s-1),X_(s-2))       & H_(n-1)(X_(s-2)) \
      H_(n+1)(X_(s+1))       & H_(n+1)(X_(s+1),X_s))          & col(#red,H_n (X_s))     & col(#red,H_n (X_s,X_(s-1))) & col(#red,H_(n-1)(X_(s-1))) \
      H_(n+1)(X_(s+2))       & H_(n+1)(X_(s+2),X_(s+1))       & H_n (X_(s+1))           & H_n (X_(s+1),X_s)           & col(#red,H_(n-1)(X_s))
    $,
    edge((-1,0), "r", "->"),
    edge((-1,1), "r", "->"),
    edge((-1,2), "r", "->"),
    edge((0,0),  "r", "->", stroke: red),
    edge((0,1),  "r", "->"),
    edge((0,2),  "r", "->"),
    edge((1,0),  "r", "->", stroke: red),
    edge((1,1),  "r", "->"),
    edge((1,2),  "r", "->"),
    edge((2,0),  "r", "->"),
    edge((2,1),  "r", "->", stroke: red),
    edge((2,2),  "r", "->"),
    edge((3,0),  "r", "->"),
    edge((3,1),  "r", "->", stroke: red),
    edge((3,2),  "r", "->"),
    edge((4,0),  "r", "->"),
    edge((4,1),  "r", "->"),
    edge((4,2),  "r", "->", stroke: red),
    edge((0,-1), "d", "->", stroke: red),
    edge((0,0),  "d", "->"),
    edge((0,1),  "d", "->"),
    edge((0,2),  "d", "->"),
    edge((2,-1), "d", "->"),
    edge((2,0),  "d", "->", stroke: red),
    edge((2,1),  "d", "->"),
    edge((2,2),  "d", "->"),
    edge((4,-1), "d", "->"),
    edge((4,0),  "d", "->"),
    edge((4,1),  "d", "->", stroke: red),
    edge((4,2),  "d", "->"),
  ),
  caption: [Staircase Diagram. @ss[p. 522]],
) <staircase>

#grid(
  columns: (auto,auto),
  gutter: 1em,
  align: horizon,
  definition(title: [(Exact Couple) @ss[p. 522]])[
    Write the preceding staircase diagram (@staircase) concisely as the right triangle, an _exact couple_, where
    $
      A_(s,t) &:= H_(s+t) (X_s), quad
      &A &:= plus.big_(s,t) A_(s,t), \
      E_(s,t) &:= H_(s+t) (X_s, X_(s-1)), quad
      &E &:= plus.big_(s,t) E_(s,t).
    $
    and $i$, $j$ and $k$ form the long exact sequences (@long_exact_homology).
    Define a _differential_ $d := j k: E_(s,t) -> A_(s-1,t) -> E_(s-1,t)$.
  ],
  diagram(
    spacing: (1em, 2em),
    $
      A &   & A \
        & E &
    $,
    edge((0,0), "rr", "->", $i$),
    edge((2,0), "dl", "->", $j$, left),
    edge((1,1), "ul", "->", $k$, left),
  ),
)

/* Degrees of $i$, $j$, $k$:
 *
 * $i: A_(s,t) -> A_(s+1,t-1)$,
 * $j: A_(s,t) -> E_(s,t)$,
 * $k: E_(s,t) -> A_(s-1,t)$.
 */

Note that all corners of the triangle are exact and $d^2 = j k j k = 0$, since $k j = 0$.
Thus we can take homology $ker d slash im d$:

#definition(title: [(Derived Couple) @ss[p. 522]])[
  #grid(
    columns: (40%,auto),
    gutter: 1em,
    [
      - $E' := ker d slash im d$,
      - $A' := i(A) subset.eq A$,
    ],
    [
      - $i' := i|_A'$,
      - $j'(i a) := [j a] in E'$ (why well-defined?),
      - $k'[e] := k e in A'$ (why well-defined?).
    ],
  )
]

/* Degrees of $i'$, $j'$, $k'$:
 *
 * $A' subset.eq A_(s+1,t-1)$,
 * $i': A'_(s,t) -> A'_(s+1,t-1)$,
 * $j': A'_(s,t) -> E'_(s-1,t+1)$,
 * $k': E'_(s,t) -> A'_(s-1,t)$.
 */

Note that $d': E'_(s,t) -> A'_(s-1,t) -> E'_(s-2,t+1)$.
Iterating the process of deriving couples leads to the sequence
$E,E',...$ with differentials $d,d',...$ called a _spectral sequence_.

== Spectra

In the construction of the Adams Spectral Sequence (@free_resolution_cohomology),
we will need a resolution of $H^*(X)$ by free $cal(A)$-modules.
$
  0 <- H^*(X) <- H^*(K_0) <- H^*(K_1) <- H^*(K_2) <- dots.c
$
This is impossible for topological spaces $K_s$, since $Sq^i (alpha) = 0$ if $i > |alpha|$ by @steenrod_squares_properties.
Spectra will fix this and more, see @homotopy_classes_abelian and @long_exact.

#definition(title: [(Spectrum) @ss[p. 584] @cat[Definition 2.6]])[
  A _spectrum_ $X$ is a family ${X_n}_(n>=0)$ of based spaces,
  together with _structure maps_ $sigma_n: Sigma X_n -> X_(n+1)$.
]

#example(title: [(Suspension spectrum functor) @cat[Definition 2.7]])[
  Define $Sigma^oo: Top -> cal(P)$ via
  $
    (Sigma^oo X)_n := Sigma^n X
    quad "and" quad
    Sigma(Sigma^n X) xarrow(id) Sigma^(n+1) X.
  $
] <suspension_prespectrum_functor>

#example(title: [(Sphere spectrum) @cat[Definition 2.8]])[
  A special case of @suspension_prespectrum_functor is $SS := Sigma^oo S^0$.
] <sphere_spectrum>

#example(title: [(Eilenberg-MacLane spectrum) @cat[Example 2.26] @ss[p. 585]])[
  Let $G$ be abelian.
  Define $X_n := K(G,n)$ and let $sigma_n: Sigma K(G,n) -> K(G,n+1)$
  be the adjoint of a CW approximation $K(G,n) -> Omega K(G,n+1)$, see @cat[Proposition 1.32].
]

#example(title: [(CW spectrum) @cat[Definition 2.27] @ss[p. 585]])[
  Let $X_n$ be based CW complexes and $sigma_n$ cellular inclusions.
  A map $f: X -> Y$ of CW spectra is a _strict_ map $X' -> Y$ for some _cofinal subspectrum_ $X'$ of $X$,
  see @ss[p. 586-587].
]

#definition(title: [(Homology of CW spectrum) @ss[p. 586]])[
  For each $n$, consider the cellular chain complex $C_*(X_n;G)$ relative to the basepoint.
  The inclusions $Sigma X_n arrow.r.hook X_(n+1)$ induce chain maps
  $
    C_* (X_n;G) tilde.equiv
    C_(*+1)(Sigma X_n;G) arrow.r.hook
    C_(*+1)(X_(n+1);G)
  $
  with a dimension shift due to suspension.
  The union
  $
    C_*(X;G) := dirlim_n C_(*+n)(X_n;G)
  $
  is the _chain complex of the CW spectrum $X$_ with a $G$ summand for each cell of $X$.
  Since homology commutes with direct limits,
  $H_i (X;G) = dirlim_n H_(i+n)(X_n;G)$.

  TODO: cohomology
]

#example(title: [(Homology of Sphere Spectrum)])[
  Recall the sphere spectrum $SS$ from @sphere_spectrum.
  $
    H_i (SS;G)
    = dirlim_n H_(i+n)(S^n;G)
    = cases(
      G\, &" if" i = 0,
      0\, &" otherwise".
    )
  $
  So $H_*(SS;G)$ contains only a copy of $G$ in degree zero.

  TODO: cohomology
] <homology_sphere_spectrum>

#definition(title: [(Homotopy for CW Spectra) @ss[p. 587]])[
  $X times I -> Y$ where $X times I$ is a CW spectrum with
  $(X times I)_n := (X_n times I)/({x_n} times I)$.
  Let $[X,Y]$ denote the set of homotopy classes of maps $X -> Y$.
]

In contrast to ordinary topological spaces:

#proposition(title: [@ss[p. 588]])[
  For CW spectra $X$ and $Y$, $[X,Y]$ is always an abelian group.
] <homotopy_classes_abelian>

#proof[
  Since every CW spectrum $X$ is equivalent to a suspension spectrum $Sigma X'$ @ss[p. 587].
  For $f,g: Sigma X -> Y$ we can define
  $
    Sigma X' xarrow("pinch")
    Sigma X' or Sigma X' xarrow(f or g)
    Y or Y xarrow(nabla)
    Y,
  $
  where $nabla$ is the fold map, inducing an additive structure on $[X,Y]$.
  Commutativity is achieved by replacing $X$ by a double suspension spectrum $Sigma^2 X''$,
  allowing for the Eckmann-Hilton argument @at[p. 340] @cat[Lemma 1.10].
]

The following result does not hold for ordinary spaces.
It's very similar to @cat[Proposition 2.42].

#theorem(title: [(Long Exact Sequence) @ss[p. 591]])[
  For a pair $(X,A)$ of CW spectra and any $Y$, there is an exact sequence
  $
    [Y,A] -> [Y,X] -> [Y,X slash A] ->
    [Y,Sigma A] -> [Y,Sigma X] -> dots.c
  $
] <long_exact>

There is an analogous result of @cat[Theorem 3.6] @at[Theorem 4.57] for CW spectra:

#theorem(title: [(Representability of $H^m (-;G)$) @ss[Proposition 5.45]])[
  There are natural isomorphisms
  $H^m (X;G) tilde.equiv [X,K(G,m)]$
  for all CW spectra $X$.
] <cw_spectra_homology_representability>

#theorem(title: [@ss[Proposition 5.46]])[
  The natural map
  $[X,or.big_i K(G,n_i)] -> product_i [X,K(G,n_i)]$
  is an isomorphism if $X$ is a connective CW spectrum of finite type and $n_i->oo$ as $i->oo$.
] <wedge_product_iso>

== Constructing the Adams Spectral Sequence

Let $X$ be a connective CW spectrum of finite type.
We construct this diagram:

/* SS Hatcher, Section 5.2, p. 594 */
#figure(
  diagram(
    spacing: (1.2em, 0.5em),
    $
      X edge(arrow.r.hook)
      &  K_0 edge("rr", ->) edge("dr", ->>)
      && K_1 edge("rr", ->) edge("dr", ->>)
      && K_2 edge("rr", ->) edge("dr", ->>)
      && dots.c \
      && K_0 slash X   =: X_1 edge("ur", arrow.r.hook)
      && K_1 slash X_1 =: X_2 edge("ur", arrow.r.hook)
      && K_2 slash X_2 =: X_3 edge("ur", arrow.r.hook)
    $
  ),
  caption: [Resolution of $X$. @ss[p. 594]],
) <resolution_X>

Choose generators $alpha_i$ for the $cal(A)$-module $H^*(X)$,
with finitely many $alpha_i$'s in each $H^k (X)$.
These determine a homotopy class $[X,K_0]$ for $K_0 := or.big_k K(G,k)$ by @cw_spectra_homology_representability and @wedge_product_iso:
$
  angle.l {alpha_i} angle.r =
  H^*(X;G) =
  product_k H^k (X;G) tilde.equiv
  product_k [X,K(G,k)] tilde.equiv
  [X, or.big_k K(G,k)]
$
We can represent $[X,K_0]$ by an inclusion $X arrow.r.hook K_0$ via a mapping cylinder @ss[Proof of Proposition 5.42]
and form the quotient $X_1 := K_0 slash X$, which is again a connective spectrum of finite type.

The associated diagram of cohomology @ss[p. 594]
#figure(
  diagram(
    spacing: (1.6em, 0.3em),
    $
      0 edge(<-)
      &  H^*(X)   edge(<<-)
      &  H^*(K_0) edge("rr", <-) edge("dr", arrow.l.hook)
      && H^*(K_1) edge("rr", <-) edge("dr", arrow.l.hook)
      && dots.c \
      &&& H^*(X_1) edge("ur", <<-)
      &&  H^*(X_2) edge("ur", <<-) \
      &&  0 edge("ur", <-)
      &&  0 edge("ur", <-) edge("ul", ->)
      &&  0                edge("ul", ->)
    $
  ),
  caption: [Free resolution of $H^*(X)$. @ss[p. 594]],
) <free_resolution_cohomology>
gives a resolution of $H^*(X)$ by free $cal(A)$-modules (TODO).

Fix a finite spectrum $Y$ and consider the functors $pi_t^Y (Z) := [Sigma^t Y,Z]$.
Applied to the cofibrations $X_s -> K_s -> X_(s+1)$, these give long exact sequences by @long_exact, forming a staircase diagram like in @staircase.
#figure(
  diagram(
    spacing: (1.6em, 1em),
    $
      col(#red,pi_t^Y X_s) & col(#red,pi_t^Y K_s) & col(#red,pi_t^Y X_(s+1)) \
      pi_(t-1)^Y X_(s-1)   & pi_(t-1)^Y K_(s-1)   & col(#red,pi_(t-1)^Y X_s)
    $,
    edge((-1,0), "r", "->"),
    edge((-1,1), "r", "->"),
    edge((0,0),  "r", "->", stroke: red),
    edge((0,1),  "r", "->"),
    edge((1,0),  "r", "->", stroke: red),
    edge((1,1),  "r", "->"),
    edge((2,0),  "r", "->"),
    edge((2,1),  "r", "->", stroke: red),
    edge((0,-1), "d", "->", stroke: red),
    edge((0,0),  "d", "->"),
    edge((0,1),  "d", "->"),
    edge((2,-1), "d", "->"),
    edge((2,0),  "d", "->", stroke: red),
    edge((2,1),  "d", "->"),
  ),
)

#definition(title: [($E_1$ page of Adams Spectral Sequence) @ss[p. 595]])[
  $
    E_1^(s,t)
    = pi_t^Y (K_s)
    = [Sigma^t Y, K_s]
    = Hom_cal(A)^0 (H^*(K_s),H^*(Sigma^t Y))
    = Hom_cal(A)^t (H^*(K_s),H^*(Y))
  $
]

$d_1: pi_t^Y (K_2) -> pi_t^Y (K_(s+1))$ is induced by $K_s -> K_(s+1)$ in the resolution of $X$ (@resolution_X),
so the $E_1$ page of the spectral sequence consists of complexes
$
  0 ->
  Hom_cal(A)^t (H^*(K_0),H^*(Y)) ->
  Hom_cal(A)^t (H^*(K_1),H^*(Y)) ->
  dots.c
$
whose homology groups are by definition
$
  E_2^(s,t)
  = Ext_cal(A)^(s,t) (H^*(X),H^*(Y)).
$

#theorem(title: [(Convergence of Adams Spectral Sequence) @ss[Theorem 5.47]])[
  For $X$ a connective CW spectrum of finite type,
  the Adams spectral sequence converges to $pi_*^Y (X)$ modulo torsion of order prime to $p$:

  #set enum(numbering: "(a)")
  + For fixed $s,t$ the groups $E_r^(s,t)$ stabilize for large $r$.
    For the filtration of $pi_(t-s)^Y (X)$ by images $F^(s,t)$ of the maps $pi_t^Y (X_s) -> pi_(t-s)^Y (X)$, we have
    $E_oo^(s,t) tilde.equiv F^(s,t) slash F^(s+1,t+1)$.

  + $inter.big_n F^(s+n,t+n)$ is the subgroup of $pi_(t-s)^Y (X)$ consisting of torsion elements of order prime to $p$.
]

== Computing a Few Stable Homotopy Groups of Spheres

Let $X = Y = SS$ and $p = 2$.

#definition(title: [(Minimal Free Resolution) @ss[p. 600]])[
  A _minimal free resolution_ of $H^*(X)$ is a free resolution of graded modules
  $
    dots.c -> F_2 -> F_1 -> F_0 -> H^*(X) -> 0,
  $
  with a minimum number of free generators for $F_i$ in each degree.
]

These allow us to compute $Ext_cal(A)^(s,t)(H^*(X),ZZ_p)$:

#lemma(title: [(Dual Complex of Minimal Free Resolution) @ss[Lemma 5.49]])[
  For a minimal free resolution, the dual boundary maps are zero in
  $
    dots.c <- Hom_cal(A)(F_2,ZZ_p) <- Hom_cal(A)(F_1,ZZ_p) <- Hom_cal(A)(F_0,ZZ_p) <- 0,
  $
  hence $Ext_cal(A)^(s,t)(H^*(X),ZZ_p) = Hom_cal(A)^t (F_s,ZZ_p)$.
]

By @homology_sphere_spectrum $H^*(SS;ZZ_2) = ZZ_2$.

TODO:
Compute $Ext_cal(A)^(s,t)(H^*(SS),ZZ_2) = Hom_cal(A)^t (F_s,ZZ_p)$
by constructing a minimal resolution of $ZZ_2$ as an $cal(A)$-module.

#bibliography("ass.yml", full: true)
