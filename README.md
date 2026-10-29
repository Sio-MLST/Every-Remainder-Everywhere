# Every Remainder Everywhere

For every modulus $N \ge 1$, every natural number $w$ not divisible by $3$, every residue $r$ and every bound $B$, there is a natural number $n > B$ with $n \equiv r \pmod N$ whose Collatz trajectory reaches $w$.
 
## Why it matters
+
+For the Collatz problem, the one familiar local modular obstruction is a root divisible by 3: nothing but doubling can lead into it, so its inverse tree is just $w, 2w, 4w, \dots$. ERE shows this is the only obstruction of its kind. For every root not divisible by 3, the inverse tree contains infinitely many numbers in every residue class modulo every $N$. The proof is fully verified in Lean 4.
+
+This does not prove or disprove the Collatz conjecture. It says that a congruence condition on the members of an inverse tree can never, by itself, exclude a number from reaching $w$. So any proof ruling out a nontrivial cycle or a divergent orbit has to use something beyond residue constraints on tree membership.
+
## Files

- [`Every Remainder Everywhere.pdf`](Every%20Remainder%20Everywhere.pdf): the paper
- [`ERE.tex`](ERE.tex): uncompiled LaTeX of the paper
- [`ERE.lean`](ERE.lean): the Lean 4 formalization (no imports; tested with Lean 4.36.0-rc1 and 4.36.0-rc2)
- [`Ring transport.html`](Ring%20transport.html): an interactive demonstration of the central trick (see below)

If you only want to understand what the result says and why it is true, read on. The proof itself is checked by the Lean file: `#print axioms every_remainder_everywhere` reports only `propext`, `Classical.choice` and `Quot.sound`. What a reader has to check by eye is that the formal statement says what the theorem above says, and that takes only the statement of `every_remainder_everywhere` and the definitions `collatz`, `iter` and `Reaches`, fewer than ten lines. Nothing below is part of the proof. It explains.

---

## What the theorem says

Take the Collatz rule: if a number is even, halve it; if it is odd, triple it and add one. Pick a target $w$ (not a multiple of 3). Now ask which numbers eventually land on $w$.

The theorem says those numbers are spread everywhere. Choose any clock size $N$, any position on that clock, and any size bound. Some number above the bound, sitting at that position, ends up at $w$.

**What it is not.** This is not the Collatz conjecture. It does not say every number reaches 1. It says the numbers that reach $w$ never systematically avoid any remainder class.

**Why not multiples of 3.** Nothing can lead into a multiple of 3 except by doubling, because "triple and add one" always leaves remainder 1 when divided by 3. So if $w$ is a multiple of 3, everything that reaches it is too.

## Running the rule backwards

Instead of following a number forward, ask who can arrive at a given number $n$. There are at most two answers:

- $2n$, because halving $2n$ gives $n$.
- $(n-1)/3$, but only when that is an odd whole number. That happens exactly when $n$ leaves remainder 4 on division by 6.

The second move is only used when its result is not a multiple of 3, since a multiple of 3 can never be produced by "triple and add one". Starting from $2w$, which reaches $w$ in one step, these two moves generate a tree of numbers that flow into $w$. The question is what remainders that tree contains.

## Why remainders are awkward

Write $N = 2^a \cdot 3^b \cdot M$, where $M$ has no factor of 2 or 3. The pieces behave very differently.

On a clock of size $M$, doubling and tripling are reversible, because 2 and 3 have inverses. On a clock of size $2^a$, doubling destroys information: keep doubling and everything collapses to 0, so you cannot run it backwards cleanly. Tripling does the same on a clock of size $3^b$.

So the proof uses two tools. The $M$ part gets a careful backward analysis through the tree. The $2^a \cdot 3^b$ part gets a forward trick. The two are combined at the end.

## The $M$ part: sorting the tree into types

Every node in the tree gets a *type*: its remainder modulo a power of 3 (call it $3^{K+1}$), and whether it is even or odd. There are only finitely many types.

For each type, collect the set of remainders modulo $M$ that actually occur among nodes of that type. The goal is to show that every type's set is everything. Two observations make this manageable.

**All the even types are the same size.** Doubling cycles through every non-multiple-of-3 remainder modulo $3^{K+1}$, and doubling a node gives another node in the tree. So you can chain doublings from any even type to any other, which forces their sets to have the same size.

**The sets stop changing.** Making the types finer (a bigger $K$) can only shrink these sets, and a whole number cannot shrink forever. Past some depth the sizes are constant.

Once things have settled, every backward step carries one type's set exactly onto the next, with nothing lost. On remainders modulo $M$, each step acts in a simple way: **stretch, then shift**, $t \mapsto \lambda t + \beta$. Doubling is $t \mapsto 2t$. The "undo" move is $t \mapsto (t-1)/3$.

## Loops, and the group of stretch-and-shifts

Start at one fixed base type and wander through other types using these moves, then come back. The stretch-and-shift you have accumulated along the way permutes the base type's remainders. All the maps you can get from closed loops form a group (undoing a loop is another loop). Call it the holonomy group.

If that group contains $t \mapsto t+1$, we are done. Sliding by 1 repeatedly reaches every remainder, so the base set is everything, and equal sizes then make every type's set everything. So the whole $M$ part is about getting a $+1$ out of the loops.

## The thing that could go wrong

There is one scenario where the tree would be non-uniform. Suppose a single remainder is left untouched by every loop. Then you could label every type with a forced remainder (the one you would have after walking there from the base), and every move in the tree would agree with those labels. That would be a hidden rigid pattern: each type tied to one specific remainder, instead of the mixing we want. The paper calls this a *flat assignment*.

The proof shows that no flat assignment exists, whenever the clock $M$ is more than trivial. It follows what such a labelling would force:

1. The base type is forced to carry remainder 1. Doubling then forces the type containing $2^j$ to carry remainder $2^j$, and the types that are powers of 4 to carry the matching power of 4.
2. A specially chosen type has two exits that land in types differing by exactly $2 \cdot 3^{K-1}$ doublings. Both exits must carry the same label, so $4^{3^{K-1}} = 1$ on the clock. So 4 has to cycle back to 1 with a period that is a power of 3.
3. A second pair of linked types finishes it. One is forced to carry remainder 4, so its exit type must carry 1. But that exit sits at a 3-adic position where powers of 4 have not yet returned to 1, so it cannot carry 1.

Every single move obeys the rules. Only the full picture is impossible.

## Why "no fixed remainder" is not quite enough

You might hope this finishes the job. It does not, and there is a concrete warning. On a clock of size 55, the map $t \mapsto 36t + 11$ has no fixed point and generates a small group, yet the only pure shift in that group is the identity. So the absence of a common fixed remainder does not by itself hand you $+1$.

The fix is one explicit loop with a handy property. The loop is: double, double, undo, double, un-double. Its net effect is a stretch by $4/3$ around the remainder 1, so it leaves 1 where it is. The key fact is that $4/3 - 1 = 1/3$ is invertible on the clock, so this stretch never collapses anything. Call this loop $w_0$.

Now take any loop $k$ in the group and do: $k$, then $w_0$, then $k$ backwards, then $w_0$ backwards. The stretches cancel, and what is left is a **pure shift**. The size of that shift measures how far $k$ moves the remainder 1.

All the pure shifts in the group form a regular pattern: all multiples of some number $q$ dividing $M$. Suppose $q$ is bigger than 1. Look at everything through the coarser clock of size $q$. Every shift is now invisible, so by the measurement above every loop leaves 1 alone. That is exactly the forbidden flat pattern, now on the smaller clock. It was shown impossible, so $q = 1$, and $+1$ is in the group.

## From $+1$ to everything

The base type's set is closed under $+1$, so it is the whole clock. All the types have the same size, so they are all full. In every 3-adic position, every remainder modulo $M$ occurs among tree nodes.

## The 2s and 3s in $N$

For the $2^a \cdot 3^b$ part, the proof stops going backwards and runs the Collatz rule forwards. Here it is convenient to count "triple, add one, then halve" as a single step, so every step halves. Choose the first few even/odd decisions of $n$ in advance. That pins down $n$ modulo a power of 2. After those steps the result has a clean form:

$$e + 3^j \cdot t$$

where $j$ is how many of the chosen steps were odd, and $t$ is the part of $n$ left free. The shape comes from every step halving the free part and each odd step also tripling it: after the prefix, the power of 2 is used up and a power of 3 is left.

The prefix is chosen to include at least one odd step. That matters because "triple and add one" always leaves remainder 1 modulo 3, and after that nothing can make the number a multiple of 3. So the output is a number the backward tree can actually contain.

Now the $M$ result takes over. It guarantees a tree node sitting at exactly the needed position modulo $3^{j+b}$ and modulo $M$. Read off $t$ from that node, build $n$ from the chosen prefix and $t$, and $n$ runs down the forward steps to that node and then on to $w$. The Chinese remainder theorem stitches the 2-part, the 3-part and the $M$-part into one remainder modulo $N$.

## The shape of the whole argument

1. Split the clock into a reversible part ($M$) and a part where information is destroyed (the 2s and 3s).
2. On the reversible part, sort the tree into finitely many types, and see that each step acts as a stretch-and-shift.
3. Rule out a hidden rigid pattern, using the fact that powers of 4 behave rigidly in the 3-adic world.
4. Use one clever loop, with commutators, to turn "no rigid pattern" into "you can slide by 1".
5. Sliding by 1 reaches everything.
6. For the rest of the modulus, work forwards, and fit the two directions together.

Running the backward steps modulo $N$ looks like chaos. On the part of $N$ where things are reversible, the chaos turns out to be a group of very ordinary stretch-and-shift maps, and the proof shows that group is large enough to reach everything.

---

## The demonstration: `Ring transport.html`

The demo lets you watch step 4, the commutator trick, happen. Open the file in a browser. (GitHub shows `.html` files as source, so download it, or serve it with GitHub Pages.)

**What you are looking at.**

- **The ring.** The residues $0, 1, \dots, M-1$ are beads on a circle, each with its own colour. Bead $t$ starts at position $t$. Applying a stretch-and-shift $t \mapsto at + b$ moves bead $t$ to position $at + b$. A rigid rotation ($a = 1$) keeps neighbouring colours next to each other. Anything else scrambles them. The bar under the ring ("order") shows how much of the original neighbour order is still intact.
- **The floor diagram.** Twelve states: the six non-multiples of 3 modulo 9, each with an even and an odd version. This is the type graph at depth $K = 1$. Filled circles are even, hollow ones odd. Solid arrows are doubling edges. Dashed arrows are the "undo" edges, labelled by the number $e$ they act on (4, 7, 13, 16, 22, 25). The dot shows where the walk currently is. Every walk starts and ends at state $(1, 0)$.
- **The readout.** The stretch-and-shift accumulated so far, as $t \mapsto at + b \pmod M$, and a plain-language description of it: identity, rigid rotation, or scramble.
- **The modulus chips.** Choose $M$ from 7, 11, 13, 17, 19, 25, 35, all coprime to 6, as the proof requires.

**What to try.** On the ring, a pure shift shows up as a rigid rotation: every bead moves the same number of places and the colour wheel stays intact.

1. Press **Around w₀**. The five-step loop plays: double, double, undo, double, un-double. The ring is scrambled by the stretch of $4/3$, but the bead at position 1 stays put while the rest jump around it. The readout names the fixed point.
2. Press **Reset**, then **Commutator**. It plays $k$, then $w_0$, then $k^{-1}$, then $w_0^{-1}$. Every bead is shuffled along the way, and at the end the beads land as an intact colour wheel, only turned. That moment of shape lost and then recovered is the stretches cancelling, leaving a pure shift. The readout reports the rotation, and the beads pop when it lands.
3. Press **Commutator** again. Each press clicks the wheel forward by the same amount, and the counter at the bottom keeps the net rotation. When the shift shares no factor with $M$, repeating it visits every position. That is the "$+1$ reaches everything" step, seen directly.

**Two cases worth trying.**

- **$M = 7$, with the rim loop as $k$.** The commutator comes back as the identity and nothing moves. The rim loop is six doublings, which multiply by $64$, and $64 \equiv 1 \pmod 7$, so on this ring the rim loop does nothing in the first place. Now switch $k$ to the $e = 22$ portal loop. The same commutator gives a real rotation by 2. So one loop's commutator can come up empty.
- **$M = 35$.** Here no commutator comes up empty, but a single one can still be too small. The rim loop gives a rotation by 28, which shares the factor 7 with 35, so pressing it repeatedly only visits 5 positions. The $e = 13$ loop gives 20 (shares the factor 5). The $e = 22$ and $e = 7$ loops give 16 and 9, and each of those reaches every position on its own. What matters is the set of all shifts you can get across all loops, and whether together they reach $1$. This is the "subgroup of shifts" argument in the proof, and the reason it needs $q = 1$ and not just one lucky loop.

**Why $w_0$ and not any loop.** In this kind of group, the commutator of any two loops is a pure shift, because the stretches always cancel. What $w_0$ adds is that its stretch $4/3$ satisfies $4/3 - 1 = 1/3$, which is invertible. That makes the size of the shift tell you exactly how far $k$ moves the point 1: $k(1) = 1 + 4\ell\tau$, where $\ell$ is $k$'s stretch and $\tau$ is the shift. So a zero shift means $k$ fixes 1, and a flat assignment is what you get when every loop fixes it.

**What the demo is, and is not.** It shows the algebra of one fixed loop $w_0$ and a handful of sample loops $k$ on the twelve-state graph at depth 1. It makes the mechanism visible: stretches cancel in a commutator and leave a pure shift. It does not show the tree itself, the stabilization argument, or the impossibility of a flat assignment. Those are in the paper, and checked in the Lean file.
