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

#let theorem    = fancy_mathblock(blocktitle: "Theorem")
#let definition = fancy_mathblock(blocktitle: "Definition")
#let example    = plain_mathblock(blocktitle: "Example")
#let corollary  = plain_mathblock(blocktitle: "Corollary")

#let cup     = math.op("⌣")
#let colim   = math.op("colim")
#let dirlim  = $limits(display(lim_(#pad(top: -0.9em, bottom: -0.3em, math.stretch(math.arrow, size: 1.1em)))))$
#let Ext     = math.op("Ext")
#let Hom     = math.op("Hom")
#let Sq      = math.op(math.italic("Sq"))
#let Top     = $bold("Top"_*)$
#let LMod(r) = $#(r)bold("-Mod")$

#let col(color, x) = text(fill: color)[$#x$]

#align(center, context [
  #set par(justify: false)
  #text(size: 20pt, smallcaps(document.title))

  #document.author.join(h(3em))
  #v(2em)
])

#outline()

= Suspension and Smash Product

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

Reduced suspension yields a canonical base point $[(x_0, t)]$.
For $f: X -> Y$ the product map $f times id$ factors through $S$ and $Sigma$ inducing $Sigma f: Sigma X -> Sigma Y$.

#definition(title: [(Suspension Homomorphism) @cat[Definition 1.26]])[
  Let $(X,x_0)$ be a space.
  The _suspension homomorphism_ is a natural transformation $Sigma: pi_n => pi_(n+1) compose Sigma$ defined by
  $
    Sigma: pi_k (X,x_0) &-> pi_(k+1)(Sigma X, [x_0 times I]) \
    [f]                &|-> [Sigma f].
  $
]

#definition(title: [(Smash Product) @cat[Definition 1.28]])[
  Let $or$ denote the wedge sum.
  By slight abuse of notation
  $
    X and Y
    := (X times Y)/(X times {y_0} union {x_0} times Y)
    = (X times Y)/(X or Y).
  $
] <smash_product>

#example[
  $X and S^k = Sigma^k X$.
] <smash_product_reduced_suspension>

= Cohomology and the Ext Functor

#definition(title: [(Cohomology Groups) @at[p. 191]])[
  Let $C$ be a chain complex and denote the $n$-th _cochain group_ by $C_n^* := Hom_R (C_n,M)$.
  For a boundary map $partial: C_n -> C_(n+1)$,
  define the _coboundary map_ $delta(phi) := partial^*(phi) = phi compose partial$.
  $
    dots.c <-
    C_(n+1)^* xarrow(sym: <-, delta)
    C_n^* xarrow(sym: <-, delta)
    C_(n-1)^* <-
    dots.c
  $
  Define the $n$-th _cohomology group_ $H^n (C;G) := ker delta_(n+1) slash im delta_n$.
]

#definition(title: [($Ext$ functor) @at[p. 195]])[
  Choose a free resolution $F$ of $M$, an exact sequence
  $
    dots.c -> F_2 xarrow(f_2) F_1 xarrow(f_1) F_0 xarrow(f_0) M -> 0,
  $
  with each $F_i$ a free $R$-module.
  Apply $Hom_R (-,N)$ and drop $Hom_R (M,N)$ to optain a chain complex
  $
    dots.c <-
    Hom_R (F_2,N) xarrow(sym: <-, f_2^*)
    Hom_R (F_1,N) xarrow(sym: <-, f_1^*)
    Hom_R (F_0,N) <-
    0.
  $
  The homology groups define $Ext_R^n (M,N)$.
  By @at[Lemma 3.1. (b)] these do not depend on the choice of $F$.

  Write $Ext_R (M,N) := Ext_R^1 (M,N)$.
]

#theorem(title: [(Universal Coefficient Theorem) @at[Theorem 3.2]])[
  $
    0 -> Ext(H_(n-1)(C),G) -> H^n (C;G) -> Hom(H_n (C),G) -> 0
  $
  is split exact.
] <uct>

#theorem([Properties of Ext @at[p. 195]])[
  - $Ext(H plus.circle H',G) tilde.equiv Ext(H,G) plus.circle Ext(H',G)$
  - $Ext(H,G) = 0$ if $H$ is free.
  - $Ext(ZZ_n,G) tilde.equiv G slash n G$.
] <ext_properties>

#example(title: "(Cohomology of Spheres)")[
  Remember that
  $
    H_m S^n =
    cases(
      ZZ\, &" if" m in {0,n},
      0\,  &" otherwise".
    )
  $
  Note that both $ZZ$ and $0$ are free.
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

#definition(title: [(Cup Product) @at[p. 206]])[
  The _cup product_ $phi cup psi in C^(k+ell)(X;R)$ of $phi in C^k(X;R)$ and $phi in C^(ell)(X;R)$ is defined for a singular simplex $sigma colon Delta^(k+ell) arrow.r X$ as
  $
    (phi cup psi)(sigma)
    = phi(sigma|[v_0,...,v_k]) dot psi(sigma|[v_k,...,v_(k+ell)]).
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

#definition(title: [(Relative Cross Product) @at[p.~215]])[
  Let $p_1: X times Y ->> X$ and $p_2: X times Y ->> Y$ be the canonical projections.
  $
    times:
    H^*(X,A;R) times.circle_R H^*(Y,B;R)
    &-> H^*(X times Y, A times Y union X times B;R) \
    x times.circle y &|-> p_1^*(x) cup p_2^*(y)
  $
  defines the _relative cross product_.
] <relative_cross_product>

#example(title: "(Reduced Cross Product)")[
  For $(X,{x_0})$ and $(Y,{y_0})$ we get a reduced cross product
  $
    tilde(H)^*(X;R) times.circle_R tilde(H)^*(Y;R) xarrow(times) tilde(H)^*(X and Y;R),
  $
  where $X and Y$ is the smash product from @smash_product.
] <reduced_cross_product>

#theorem(title: [(Künneth formula) @at[Theorem 3.18]])[
  For CW pairs $(X,A)$ and $(Y,B)$ the relative cross product in @relative_cross_product is an isomorphism of rings
  if for all $k$, $H^k (Y,B;R)$ is a finitely generated free $R$-module.
]

#corollary(title: "(Suspension Isomorphism)")[
  Let $r$ be a generator of $H^k (S^k;R) tilde.equiv R$, see @sphere_cohomology.
  With @smash_product_reduced_suspension and @reduced_cross_product in mind we get the _suspension isomorphism_
  $
    tilde(H)^n (X;R) xarrow(tilde.equiv) tilde(H)^(n+k) (Sigma^k X;R), quad
    x |-> x times.circle r.
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
]

#theorem(title: [(Adem relations) @at[p. 496]])[
  $
    Sq^a Sq^b
    &= sum_j binom(b-j-1,a-2j) Sq^(a+b-j) Sq^j,
    &&" if " a < 2b \
    P^a P^b
    &= sum_j (-1)^(a+j) binom((p-1)(b-j)-1, a-p j) P^(a+b-j) P^j,
    &&" if " a < p b \
    P^a beta P^b
    &= sum_j (-1)^(a+j) binom((p-1)(b-j), a-p j) beta P^(a+b-j) P^j \
    &- sum_j (-1)^(a+j) binom((p-1)(b-j)-1, a-p j-1) P^(a+b-j) beta P^j,
    &&" if " a <= p b
  $
]

#definition(title: [(Steenrod Algebra) @at[p. 496]])[
  $
    cal(A)_2 :=
    (ZZ_2 angle.l Sq^1, Sq^2, dots angle.r)/"(Adem relations)"
  $
  For odd $p$ define
  $
    cal(A)_p :=
    (ZZ_p angle.l beta, P^1, P^2, dots angle.r)/("(Adem relations and" beta^2 = 0 ")")
  $
]

= The Adams Spectral Sequence and Low-Dimensional Computations

#figure(
  image("images/spectral_sequence_pages.svg", width: 100%),
  caption: [Pages of a spectral sequence and their differentials. @ss[p. 520]],
)

== Exact Couples

#definition(title: [(Filtration) @ss[p. 522]])[
  A sequence of subspaces
  $dots.c subset.eq X_p subset.eq X_(p+1) subset.eq dots.c$
  is a _filtration_ of $X := product.co X_p$.
]

By @at[Theorem 2.16] each pair $(X_p,X_(p-1))$ yields a _long exact sequence of homology_ with connecting homomorphisms $k$.
#math.equation(block: true, numbering: "(1)",
  $dots.c xarrow(k) H_n (X_(p-1)) xarrow(i) H_n (X_p) xarrow(j) H_n (X_p, X_(p-1)) xarrow(k) H_(n-1) (X_(p-1)) xarrow(i) dots.c$
) <long_exact_homology>
Considering all pairs $(X_p,X_(p-1))$ at once, we can interlock these long exact sequences in a _staircase diagram_:
#figure(
  diagram(
    spacing: (0.8em, 1em),
    $
      col(#red,H_(n+1)(X_p)) & col(#red,H_(n+1)(X_p,X_(p-1))) & col(#red,H_n (X_(p-1))) & H_n (X_(p-1),X_(p-2))       & H_(n-1)(X_(p-2)) \
      H_(n+1)(X_(p+1))       & H_(n+1)(X_(p+1),X_p))          & col(#red,H_n (X_p))     & col(#red,H_n (X_p,X_(p-1))) & col(#red,H_(n-1)(X_(p-1))) \
      H_(n+1)(X_(p+2))       & H_(n+1)(X_(p+2),X_(p+1))       & H_n (X_(p+1))           & H_n (X_(p+1),X_p)           & col(#red,H_(n-1)(X_p))
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
    $A := plus.big_(n,p) H_n (X_p)$
    and
    $E := plus.big_(n,p) H_n (X_p,X_(p-1))$
    and $i$, $j$ and $k$ form the long exact sequences (@long_exact_homology).
    Define a _differential_ $d: E -> E$ as $d := j k$.
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

Iterating the process of deriving couples leads to the sequence
$E,E',...$ with differentials $d,d',...$ called a _spectral sequence_.

== Spectra

TODO @ss[p. 588]:
One way in which spectra are better than spaces is that $[X,Y]$ is always an abelian group.

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
]

#example(title: [(Eilenberg-MacLane spectrum) @cat[Example 2.26] @ss[p. 585]])[
  Let $G$ be abelian.
  Define $X_n := K(G,n)$ and let
  $
    sigma_n: Sigma K(G,n) -> K(G,n+1)
  $
  be the adjoint of a CW approximation $K(G,n) -> Omega K(G,n+1)$, see @cat[Proposition 1.32].
]

TODO: Are CW approximations weak equivalences? Is it an $Omega$-spectrum?

#example(title: [(CW spectrum) @cat[Definition 2.27] @ss[p. 585]])[
  Let $X_n$ be based CW complexes and $sigma_n$ cellular inclusions.
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
]

#definition(title: [(Mapping Cylinder of Cellular Map)])[
  Let $f: X -> Y$ be a cellular map of CW spectra.
  Pass to a strict map (TODO).

  #figure(
    image("images/mapping_cylinder.svg", width: 20em),
    caption: [Mapping cylinder $M_f := ((X times I) union.sq Y)/((x,1) ~ f(x))$.],
  )
] <mapping_cylinder>

Very similar to @cat[Proposition 2.41]:

#theorem(title: [(Long exact sequence) @ss[p. 591]])[
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
We can represent $[X,K_0]$ by an inclusion $X arrow.r.hook K_0$ via a mapping cylinder @mapping_cylinder
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
)
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
    edge((2,1),  "r", "->"),
    edge((0,-1), "d", "->", stroke: red),
    edge((0,0),  "d", "->"),
    edge((0,1),  "d", "->"),
    edge((2,-1), "d", "->"),
    edge((2,0),  "d", "->", stroke: red),
    edge((2,1),  "d", "->", stroke: red),
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
    $
      E_oo^(s,t) tilde.equiv F^(s,t) slash F^(s+1,t+1).
    $

  + $inter.big_n F^(s+n,t+n)$ is the subgroup of $pi_(t-s)^Y (X)$ consisting of torsion elements of order prime to $p$.
]

== Computing a Few Stable Homotopy Groups of Spheres

TODO

#bibliography("ass.yml", full: true)
