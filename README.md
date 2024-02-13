Left-leaning red-black trees in Agda
====================================

This is an implementation of red-black trees (aka 2-3-4 trees) in Agda with static balancing and ordering invariants.
Insertion and deletion are implemented, the latter just for left-leaning red-black trees (aka 2-3 trees).

The development was mostly carried out by Julien Oster as a student research project at LMU Munich in 2009/2010.

The main development resides in [LLRBTree.agda](RBTree/LLRBTree.agda).

The implementation of the ordering invariant predates the seminal paper by Conor McBride, _Keeping your neighbours in order_ (ICFP 2010).  The techniques of McBride would considerably simplify the development.
