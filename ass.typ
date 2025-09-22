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
#set par(justify: true)
#set text(font: "New Computer Modern")

#show heading: smallcaps
#show heading: set text(weight: "regular")
#show link: text.with(fill: blue)
#show sym.colon: math.class("fence", sym.colon)

#let theorem    = fancy_mathblock(blocktitle: "Theorem")
#let definition = fancy_mathblock(blocktitle: "Definition")
#let example    = plain_mathblock(blocktitle: "Example")
#let corollary  = plain_mathblock(blocktitle: "Corollary")

#let cup     = math.op("⌣")
#let colim   = math.op("colim")
#let Ext     = math.op("Ext")
#let Hom     = math.op("Hom")
#let Sq      = math.op(math.italic("Sq"))
#let Top     = $bold("Top"_*)$
#let LMod(r) = $#(r)bold("-Mod")$

#let col(color, x) = text(fill: color)[$#x$]


#align(center, context [
  #text(size: 20pt, smallcaps(document.title))

  #document.author.join(h(3em))
  #v(2em)
])

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

/* SS Hatcher, Section 5.2, p. 580 */
$
  [Y,X] &-> Hom_cal(A)(H^*(X),H^*(Y))
$
where $H^*(X)$ is viewed as a graded left module over $cal(A)$.
TODO: Does Hatcher mean
$
  [Y,X] &-> Hom_cal(A)_p (H^*(X;ZZ_p),H^*(Y;ZZ_p)) ?
$

== Spectra

TODO @ss[p. 588]:
One way in which spectra are better than spaces is that $[X,Y]$ is always an abelian group.

#definition(title: [(Prespectra) @cat[Definition 2.6]])[
  A _prespectrum_ $E$ is a family ${E_n}_(n>=0)$ of based spaces,
  together with _structure maps_
  #grid(
    columns: (auto,auto),
    gutter: 1.5em,
    [
      $
        sigma_n: Sigma E_n -> E_(n+1).
      $
      A map $f: E -> E'$ of prespectra is a family ${f_n}_(n>=0)$ satisfying the commutativity of the right diagram.
      Prespectra form a category $cal(P)$.
    ],
    [
      #v(-1.5em)
      #diagram(
        $
          Sigma E_n & Sigma E'_n \
          E_(n+1)   & E'_(n+1)
        $,
        edge((0,0), "r", "->", $Sigma f_n$, left),
        edge((0,0), "d", "->", $sigma_n$),
        edge((0,1), "r", "->", $f_(n+1)$),
        edge((1,0), "d", "->", $sigma'_n$, left)
      )
    ]
  )
]

#example(title: [(Suspension prepectrum functor) @cat[Definition 2.7]])[
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

#example(title: [(CW spectrum) @cat[Definition 2.27] @ss[p. 585]])[
  Let $X_n$ be based CW complexes and $sigma_n$ cellular inclusions.
]

#example(title: [(Eilenberg-MacLane spectrum) @cat[Example 2.26] @ss[p. 585]])[
  TODO
]

#definition(title: [(Homotopy Groups of Prespectra) @cat[Definition 2.23]])[
  For a prespectrum $E$ define the telescope
  #v(-1em)
  $
    pi_(n+k)(E_k) xarrow(Sigma)
    pi_(n+k+1)(Sigma E_k) xarrow((sigma_k)_*)
    pi_(n+k+1)(E_(k+1)).
  $
  Now define $pi_n (E) := colim_k pi_(n+k)(E_k)$.
]

#definition(title: [(Homology of CW spectrum) @ss[p. 586]])[
  TODO
]

#definition(title: [(Mapping Cylinder of Cellular Map])[
  Let $f: X -> Y$ be a cellular map of CW spectra.
  Pass to a strict map (TODO).

  #figure(
    image("images/mapping_cylinder.svg", width: 20em),
    caption: [Mapping cylinder $M_f := ((X times I) union.sq Y)/((x,1) ~ f(x))$.],
  )
]

There is an analogous result of @cat[Theorem 3.6] @at[Theorem 4.57] for CW spectra:

#pagebreak()
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
We construct this diagram @ss[p. 594]:

/* SS Hatcher, Section 5.2, p. 594 */
#align(
  center,
  diagram(
    spacing: (1.2em, 0.5em),
    $
      X edge(->)
      &  K_0 edge("rr", ->) edge("dr", ->)
      && K_1 edge("rr", ->) edge("dr", ->)
      && K_2 edge("rr", ->) edge("dr", ->)
      && dots.c \
      && K_0 slash X   =: X_1 edge("ur", ->)
      && K_1 slash X_1 =: X_2 edge("ur", ->)
      && K_2 slash X_2 =: X_3 edge("ur", ->)
    $
  )
)

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
By TODO, we can represent $[X,K_0]$ by an inclusion $X arrow.r.hook K_0$
and form the quotient $X_1 := K_0 slash X$, which is again a connective spectrum of finite type.

The associated diagram of cohomology @ss[p. 594]
/* SS Hatcher, Section 5.2, p. 594 */
#align(
  center,
  diagram(
    spacing: (1.6em, 0.3em),
    $
      0 edge(<-)
      &  H^*(X)   edge(<-)
      &  H^*(K_0) edge("rr", <-) edge("dr", <-)
      && H^*(K_1) edge("rr", <-) edge("dr", <-)
      && dots.c \
      &&& H^*(X_1) edge("ur", <-)
      &&  H^*(X_2) edge("ur", <-) \
      &&  0 edge("ur", <-)
      &&  0 edge("ur", <-) edge("ul", ->)
      &&  0                edge("ul", ->)
    $
  )
)
gives a resolution of $H^*(X)$ by free $cal(A)$-modules.

#definition(title: [($E_1$ page of Adams Spectral Sequence) @ss[p. 595]])[
  $
    E_1^(col(#red,s),col(#blue,t))
    = pi_col(#blue,t)^Y(K_col(#red,s))
    = [Sigma^col(#blue,t) Y, K_col(#red,s)]
    = Hom_cal(A)^0 (H^*(K_col(#red,s)),H^*(Sigma^col(#blue,t) Y))
    = Hom_cal(A)^col(#blue,t) (H^*(K_col(#red,s)),H^*(Y))
  $
]

In general, the differentials are maps $d_r: E_r^(s,t) -> E_r^(s-1,t+r)$ (TODO induced?).
$d_1: pi_t^Y (K_2) -> pi_t^Y(K_(s+1))$ is induced by $K_s -> K_(s+1)$ in the resolution of $X$ (TODO link),
so the $E_1$ page of the spectral sequence consists of complexes
$
  0 ->
  Hom_cal(A)^col(#blue,t) (H^*(K_col(#red,0)),H^*(Y)) ->
  Hom_cal(A)^col(#blue,t) (H^*(K_col(#red,1)),H^*(Y)) ->
  dots.c
$
whose homology groups are by definition
$
  E_2^(col(#red,s),col(#blue,t))
  = Ext_cal(A)^(col(#red,s),col(#blue,t)) (H^*(X),H^*(Y)).
$

#theorem(title: [(Convergence of Adams Spectral Sequence) @ss[Theorem 5.47]])[
  For $X$ a connective CW spectrum of finite type,
  the Adams spectral sequence converges to $pi_*^Y(X)$ modulo torsion of order prime to $p$:

  #set enum(numbering: "(a)")
  + For fixed $s,t$ the groups $E_r^(s,t)$ stabilize for large $r$.
    TODO

  + $inter.big_n F^(s+n,t+n)$ is the subgroup of $pi_(t-s)^Y (X)$ consisting of torsion elements of order prime to $p$.
]

#bibliography("ass.yml", full: true)
