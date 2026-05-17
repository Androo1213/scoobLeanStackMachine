import VersoManual

open Verso.Genre Manual

#doc (Manual) "Introduction" =>

I'm in an odd spot. After four years, I cling to a love for compilers. Its quite different from my AI gun-ho peers, matrix multiplication sitting in the holsters
milling through Soda, ready to fire a training round to deduce the best token output for a conversation with a passerby.
Anyways, not only do I not have an intellectual affinity for this sub-study, but I also sort of despise
the tokenization at the heart of LLMs, fundamentally reflecting a mechanism of decontextualization, leading to-- well vast generisism-- perhaps soulessness, or great maybe ecstasy in regards to the newfound tool to remove the profit-hindering artistic and artisan side of it all that used to make it well- cool.
Anyways. Why do I love compilers? I'm not so sure myself, and it seems disheartening to want to make a tool which lies under the apparent fervour of programs made to train these machines, or programs output by these same machines.

Maybe it was my formative years where I mainly studied latin and greek, and fell in love with meticuously looking at essentially syntatically alien symbols and syntax, only to have my parents
move to silicon valley where tablets went from stone to glass. Anyways, during college, anyone that knows me, knows I've become a Java fanatic (or apologist to some),
and much of my time has been spent working on and studying the JIT. In the winter I was digging into Graal's
Sea of Nodes and became entranced. Anyways, then as the semester started I found myself learning Rust on the side to try and make 162
less of a perpetual onus (which still didn't help), and was then quite excited to see when looking at Rust's compiler optimisations
that my 263 professor, essentially spearheads `egg` which rewrites expressions to all equivalent forms and then selects the 'best' one according to some cost function.
Anyways,

I got hooked looking from afar at this complicated library written in a language that I didn't really (and still don't) know very well.
So, for my final project for 263-- trying to avoid any hubris in claiming my project really even chips away at `egg`-- wanted to take a shot at at least using Lean to help show that rewrites on a tiny language maintained
equivalence, and found some rewrite branches to be better than other. As such, I've made a tiny stack machine in Lean. It has six instructions: push, add, mul, dup, pop, swap, a stack that holds symbolic expression trees rather than raw integers,
and an evaluator that resolves them against an environment. On top of these instructions are a set of rewrites, to make the space of programs one is able to write, suddenly so blazing fast. These rewrites were
add zero, multiply by one, fold two literals, drop a push-pop pair, and strength-reduce.

Originally, I thought to have the stack just held integers. But comparing two programs of this sort boils down to a glorified lists of numbers comparison, and there's nothing to prove. So I ended up having the stack hold symbolic Expr trees instead,
and made equivalence defined as eval-equality under any environment. For that to happen, I made the per-rule theorems, an optimise function and its soundness theorem. Then I made a brute-force equality saturation
variant that enumerates every reachable rewrite w/in a depth bound, and asserts the most optimised program to be the smallest tree representation.

Anyways, in thinking of names for the project, I thought of quail, as a well-known very tiny egg, and then Bee Hummingbird (the bird with the smallest egg), but in the end I thought peepProof was sort of cute.
This project really uses peephole optimiser as it walks through my bytecode-esque language, replacing short instruction sequences with provably equivalent shorter ones. Thus I have 'peep'. A chick makes the 'peep' sound, which is small,
as is this project and language, and, a chick is vaguely related to an `egg`, and as such, I've come full circle. Oh, and of course, proof is appended, for alliterative, lengthening, and general obvious reasons.
