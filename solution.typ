#let title = "DiD It (2023 CryptoCTF) -- Solution"
#let author = "Ben Herzog"
#import "@preview/ctheorems:1.1.0": *
#show: thmrules
#set heading(numbering: "1.1")
#show link: underline

#set document(
    title: title,
    author: author
)

#let theorem = thmbox(
  "theorem",
  "Theorem",
  fill: rgb("#e8e8f8")
)
#let lemma = thmbox(
  "theorem",            // Lemmas use the same counter as Theorems
  "Lemma",
  fill: rgb("#efe6ff")
)
#let corollary = thmbox(
  "corollary",
  "Corollary",
  base: "theorem",      // Corollaries are 'attached' to Theorems
  fill: rgb("#f8e8e8")
)

#let remark = thmbox(
  "remark",
  "Remark",
  fill: rgb("#f8e8e8")
)

#let definition = thmbox(
  "definition",         // Definitions use their own counter
  "Definition",
  fill: rgb("#e8f8e8")
)

#let exercise = thmbox(
  "exercise",
  "Exercise",
  stroke: rgb("#ffaaaa") + 1pt,
  base: none,           // Unattached: count globally
).with(numbering: "I")  // Use Roman numerals

// Examples and remarks are not numbered
#let example = thmplain("example", "Example").with(numbering: none)
#let remark = thmplain(
  "remark",
  "Remark",
  inset: 0em
).with(numbering: none)

// Proofs are attached to theorems, although they are not numbered
#let proof = thmplain(
  "proof",
  "Proof",
  base: "theorem",
  bodyfmt: body => [
    #body #h(1fr) $square$    // Insert QED symbol
  ]
).with(numbering: none)

#let solution = thmplain(
  "solution",
  "Solution",
  base: "exercise",
  inset: 0em,
).with(numbering: none)
#set align(center)
#text(17pt, weight: "bold")[#title]

#text(10pt)[#author, #datetime.today().display()] 

#set align(left)

#outline()

= The Challenge

#definition[
The "DiD Game" with parameters $(n, l, q)$ is a game for one player played in the following way. 
- A secret set $K subset.eq NN_n$ with $|K|=l$ is picked at random.
- The player can then make $q$ _queries_ $Q_0, Q_1, dots, Q_(q-1)$. Each query is of the form $Q_i subset.eq NN_n$.  
- After sending each query $Q_i$ the player receives that query's _response_ $R(Q_i)$, which is computed in the following way: each $w in Q_i$ is assigned a random per-query secret value $e_w in {0,1}$, and then $R(Q_i) = {(w^2+e_w)_(mod n) | w in Q_i without K}$.
- If the player can guess $K$ within their alloted queries (that is, if for any $0 lt.eq i lt l$ we have $Q_i=K$) then the player wins. Otherwise, the player loses.
]
The exercise calls for a winning strategy for the DiD game with $n=127$, $l=20$, $q=11$.


= Preliminary Discussion <strategy>


Somewhat counter-intuitively, the 'reasonable' way to get an initial grasp on this problem doesn't get involved very much with the specific ring structure of $frac(ZZ, n ZZ)$, the behavior of $f(k) = k^2$ or the error term $e_m$. Instead, it contends with the basic structure of repeatedly sending a query $S$ and obtaining $f(S without K)$, and mainly with the fact that $f$ is not a bijection (that is: we can have $f(x_1)=f(x_2)$ but $x_1 eq.not x_2$).

To understand how central $f$ not being bijective is to the challenge posed here, we will show how $f$ being a bijection would have trivialized the problem.

#theorem[
  Consider a variation of the DiD game where instead of $f(x) = x^2$, $f$ is some nondeterministic bijection (meaning there is an error term $e_k$, but we are still guaranteed that $f(x_1)=f(x_2) arrow x_1 = x_2$). Then there is a winning strategy for this game using 2 queries.
  #proof[Take the first query to be $Q_0 = NN_n$, obtain the response $R(Q_0)$ and then immediately compute $ Q_1 = f^(-1)({x in NN_n | exists.not y in R(Q_0): f^(-1)(x) = f^(-1)(y)}) = K $ Informally, every value $f(x)$ immediately "incriminates" the original value of $x$ that induced it -- the other possible values of $f(x)$ that might have occurred don't mitigate that. So, by analogy, the set of values $f(Q_0 without K)$ "incriminates" (determines) the original set $(Q_0 without K)$, and thus immediately $K$ as well, since $K subset.eq Q_0$ and $Q_0$ is known.
]
] <bijection_strategy>

Clearly, being able to invert $f$ is a powerful tool for defusing this sort of problem. Alas, the original problem has a non-invertible $f$. Can we somehow rescue this approach? Can we do the impossible, and invert the non-invertible?

= Branch Inversion

Actually, chances are you've already seen how to do it back in seventh grade. The arcane operation known as a "square root" is somehow the inverse of the non-invertible function $f(x) = x^2$. This strange feat of alchemy is pulled off by breaking $f$'s domain $D$ into several _branches_. 

#definition[Let $f: D arrow R$ a function. Some $B subset.eq D$ is said to be a _branch_ of $f$ if for all $x_1, x_2 in B$, $f(x_1) = f(x_2)$ implies $x_1 = x_2$ (that is, the restriction of $f$ to $B$ is a bijection). A set of branches ${B_i}_(i=0)^n$ that are disjoint with $union_(i=0)^n B_i = D$ is called a _branch decomposition_ for $f$ in $D$.] <branch_definition>


Specifically for $f(x)=x^2$, it is customary to break down its domain $RR$ into 2 branches, $(-infinity, 0)$ and $[0, infinity)$. $f$ is injective if its domain is one of those branches, instead of the whole of $RR$. Thus we obtain one $f^(-1)$ candidate per branch, and two in total. One of these is the aforementioned "principal square root", and the other is ignored #footnote[Presumably so that one day it may come back to haunt the first, shouting "look at me, brother! I'm you! I'm your SHADOW!"]. 

#theorem[Let $f: D arrow R$ a function. Then there is a branch decomposition for $f$ in $D$.
#proof[
 Take every $x in D$ to be its own separate branch.]
] <branch_decomposition_exists>

But we are naturally interested in branch decompositions with a finite number of branches, and ideally as few as possible.

#definition[Let $f: D arrow R$ a function. The minimum number of branches required to construct a decomposition of $f$ in $D$ is called $f$'s _branch number_ in $D$.] <branch_number>

#theorem[Let $f: D arrow R$ a function. The branch number of $f$ in $D$ equals the maximum number of different $x in D$ that $f$ maps to the same value.
#proof[
  Let's call the branch number $b$ and this maximum number $k$. To prove $b=k$ we will separately prove $b lt.eq k$ and $k lt.eq b$.
  - $k lt.eq b$: By definition of $k$ there must exist $x_0, x_1, dots, x_(k-1)$ with $f(x_i)=f(x_0)$ for all $0 lt.eq i lt k$. Suppose by contradiction there's a branch decomposition with fewer than $k$ branches. Then two of these values $x_i, x_j$ (with $i eq.not j$) have to share a branch (due to what's called the 'pigeonhole principle': there are $k$ 'pigeons' trying to fit into fewer than k 'pigeonholes'). But $f(x_i)=f(x_j)$ so $x_i$ and $x_j$ sharing a branch violates the definition of a branch (@branch_definition).
  - $b lt.eq k$: For each $r in R$ number the $d in D$ that have $f(x)=r$. The result is a list $x_0, x_1, dots$ that is guaranteed to have at most $k$ values. Further, because $f$ is deterministic, a $d in D$ can only appear in the list for at most one value of $r$. Number the branches $0, 1, dots, k-1$ and assign each $x_i$ in each $r$-list branch number $i$. This results in a branch decomposition for $f$ in $D$ with $k$ branches.
]
] <branch_number_formula>

= Attacking DiD... Sort of

Working with branch decomposition hands us a winning strategy for a relaxed version of the DiD game without the error term.

#theorem[
  Consider a variation of the DiD game without the error term $e_k$, and let $b$ the branch number of $f$ in $NN_n$. There is a winning strategy for this game using $b+1$ queries, where $b$ is the branch number of $f$ in $NN_n$.
  #proof[Let ${B_i}_(i=0)^(b-1)$ a branch decomposition of $f$ in $NN_n$. Send $b$ queries with $Q_i = B_i$. By the same logic described in @bijection_strategy, the response to each $Q_i$ determines $K sect B_i$. Now compute: $ Q_b = union_(i=0)^(b-1) (K sect B_i) = K sect (union_(i=0)^(b-1) B_i) = K sect NN_n = K $.
]] <win_did_no_error_term>

How can we use this to win the real game, that has the error term $e_k$? We might try to generalize the notion of "branch" (@branch_definition) to allow for nondeterministic functions, like so:

#definition[Let $f: D arrow 2^R$ be a nondeterministic function. Some $B subset.eq D$ is said to be a _branch_ of $f$ if for all $x_1, x_2 in B$, $f(x_1) sect f(x_2) eq.not emptyset$ implies $x_1 = x_2$.]

Analogues of @branch_decomposition_exists, @branch_number and even @win_did_no_error_term emerge immediately, so we should get an easy analogue of @branch_number_formula as well, right? Well, unfortunately, not quite...

#theorem[Determining the branch number of a nondeterministic function is NP-complete. (More precisely: Consider the decision problem of determining, for a given nondeterministic $f: D arrow 2^R$ and $m in NN$, whether the branch number of $f$ in $D$ (denoted $k$) satisfies $k lt.eq m$. This problem is NP-complete.)
#proof[
  It's easy to verify a given branch decomposition with $m$ branches or fewer in polynomial time (so the problem is in NP). For NP-hardness, there's a natural reduction to this problem of a known NP-complete problem -- graph k-colorability. Number the graph's edges and vertices, then construct an $f: ZZ arrow ZZ$ which sends each vertex number to a set containing itself, as well as all numbers of edges that vertex touches. There is a straightforward one-to-one correspondence between $k$-colorings of the graph and branch decompositions of $f$ in $ZZ$ that have $k$ branches. So, the graph is $k$-colorable iff $f$'s branch number in $ZZ$ is at most $k$.
  ]
] <nondeterministic_branch_number_npc>

Informally speaking, this means that any attack on DiD that tries to make use of $f$'s nondeterministic branch number will have to either make use of $f$'s specific features ($f$ lives in $ZZ / (p ZZ)$ for a prime $p$; it squares then possibly adds 1; etc), or else be suboptimal, in the sense that it will not have access to the exact branch number.

"Suboptimal" in this case does not mean not optimal enough. Using some greedy algorithm for "efficient enough" coloring (like e.g. repeatedly taking away a maximal independent set and assigning it a color) works well enough in practice for this problem with the original challenge parameters. Doing this typically results in a game win that requires 6-7 queries.

= Properly Rescuing the Attack

How feasible is analyzing $f$ to understand its potential branch structure? The kind of problem we are looking at here tends to get very scary, very quickly. A good start would be to envision the "graph we need to color" per the analogy in @nondeterministic_branch_number_npc; $a, b in ZZ / (127 ZZ)$ will be connected by an edge (meaning, they can't be on the same branch) if $a^2 - b^2 in {-1, 0, 1}$. The case with 0 is straightforward, meaning $a$ and $-a$ are always neighbors, but what about the other cases? For $a^2 - b^2 = 1$, this would have to mean that... scribble, scribble... three hours in and you are looking at arXiv papers from 2014 that prove lower bounds on the lengths of consecutive quadratic residues modulo a prime, and asking yourself where you had gone wrong to reach this point in your life. 

Thankfully, there is a workaround that allows dealing with the issue without most of this hassle. The key insight is visualizing the graph of quadratic residues directly, repressing for a moment the way that a residue actually represents two possible square roots. 

#theorem[For all p>5,#footnote[If we allow $p lt.eq 5$ the argument is not much different; it just allows for a degenerate case where $G_1$ has chromatic number $1$ and consequently $G$ has chromatic number $2$ instead.]
 the graph $G$ induced by a DiD problem has chromatic number exactly 4.
#proof[
Consider the two graphs: $ G_1: V_1 = {b in ZZ_p | exists a in ZZ_p: a^2 = b_(mod p)} , E_1 = {{a,b} | a, b in V_1, b-a = 1 _(mod p)} $ $ G_2: V_2 = {0,1}, E_2 = {{0,1}} $
$G_2$ is the simple 2-clique and clearly has chromatic number 2. As for $G_1$, it is a sub-graph of a "circle graph" where each element of $ZZ_p$ is connected to the previous and the next; specifically, it is the sub-graph including all quadratic residues modulo $p$. But assuming $p>5$, by folk theorem there exist at least two consecutive quadratic residues and at least one quadratic non-residue modulo $p$; so $G_1$ must also have a chromatic number of $2$, since it is a union of disjoint simple paths at least one of which is more than 1 vertex long.
  Now (and this is the key insight) $G$ is in fact isomorphic to the strong product of $G_1$ and $G_2$. By a property of strong products, the product's chromatic number is at most the product of the element chromatic numbers, $2 times 2 = 4$. But clearly $G$ cannot have a chromatic number smaller than 4, since it contains 4-cliques (any 4 square roots corresponding to 2 consecutive quadratic residues). This shows its chromatic number is exactly 4.  ]
] <did_colorable>

Try drawing the graph for a sample $p$ and see its shape to become convinced of what's going on here, and the way that the fact that $G$ "is a bunch of simple paths, it's just that each node in the path is actually 2 nodes, with all the induced edges this implies" determines $G$'s chromatic number.

Understanding this structure of the graph immediately allows a winning strategy that only requires $5$ queries (a nice margin below the allotted 11). 

This is a good time to take a moment and appreciate how, using some visualization and / or the properties of graph strong products, you just "solved an NP-complete problem"! Not everything that is difficult in the general case is going to be difficult in the specific case you actually need to solve.
