# Partition jumper

This is a specialized family of algorithms which require a list to be _uniquely [partitioned](https://doc.rust-lang.org/stable/std/primitive.slice.html#method.partition_point)_ (see also [set partition](https://en.wikipedia.org/wiki/Partition_of_a_set)). These *don't need to know the predicate* (predicate-agnostic), if equality is [total](https://en.wikipedia.org/wiki/Equivalence_relation). However, knowing the predicate allows significant generalization.

> [!note]
> There is an _alternative formulation_ that uses approximate-equality, but since `≈` isn't [transitive](https://en.wikipedia.org/wiki/Transitive_relation), the list must be sorted (or at least, partitioned by approximate comparison, which makes "similar" partitions contiguous)

In general, `s` is uniquely-partitioned if **all values with a common property are contiguous**; Non-generally and informally, runs must "consolidate its representative value". Examples:
- Good: `[0,0,1,1]` (2 distinct runs)
- Bad: `[0,1,1,0]` (`1` is distinct but `0` is duped)

This implies many things:
- Any slice of `s` is uniquely-partitioned. Which implies trivial parallelization!
- Any sorted list (by the standard numeric (scalar, not vectorial) comparison-function) is uniquely-partitioned
- There cannot be more than 1 partition with the same [mode](https://en.wikipedia.org/wiki/Mode_(statistics))
- If all partitions in `s` are isometric, there's a [bijection](https://en.wikipedia.org/wiki/Bijection) between modes of `s` and its partitions

These algorithms exploit the following lemmas (theorems?):
- Multiplication is faster than repeated addition
- [Bin exponentiation](https://en.wikipedia.org/wiki/Exponentiation_by_squaring) is faster than repeated multiplication
- Iterating over all elements of a list is `O(n)`, but finding values in a sorted list can be as fast as `O(log(n))` (bin-search)

See [reference implementations here](src/ref.py). Those are designed to "complement each other", because I want them to be examples of various use-cases.

I hope that this proof-of-concept can help optimize many other programs that deal with grouped values of any type, such as a specialized [RLE](https://en.wikipedia.org/wiki/Run-length_encoding) compressor.

Most discussion about partition-jumping was on [LLVM issue #118731](https://github.com/llvm/llvm-project/issues/118731) and [this disbloat guild](https://discord.gg/programming) in the `#cs-theory` channel

> [!note]
> [I don't like disbloat](https://github.com/Rudxain/uBO-rules/blob/42220bd4f80052ee15136dff7269df19529c43ec/rx.ubo#L3-L19), but [it](https://consumerrights.wiki/w/Discord) was my only choice at the time

## Complexity analysis
TLDR: average time is `O(part_count * lb(n))`, but **it's more nuanced than that**. Best-case is `O(1)`. Worst-case is `O(n * lb(n))` (bin-search), or `O(n)` (exponential search)

The runtime of these algorithms is dominated by the boundary (partition point) count (`part_count - 1`). So for the overhead to be worthwhile, the number of unique (according to some "key function") values should be low (relative to the length of `s`)

It's worth noting that the aforementioned `lb` (bin logarithm) is misleading. The 1st bisection is `O(lb(n))` but the next is `O(lb(n - part_len_0))` then `O(lb(n - part_len_0 - part_len_1))`, and so on, until it becomes `O(lb(part_len_last))` (if we ignore the `target == s[-1]` check, which simplifies the last bisection into `O(1)`). That's only true for bin-search. For exp-search it's `O(lb(part_len_i))` (worst-case), and `O(1)` (best-case) with `target == s[-1]`.

As for the space complexity, it's `O(1)` for fixed-precision numbers. The basic implementation doesn't allocate auxiliary memory, but I'm _working on one that does_ (see below)

## Alts

### Witness tracking
The impl with aux-mem will use a data-structure to track the known "sub-partitions" that it encounters while bisecting (I call those "witnesses" or "bystanders"). For example:

`s := [0,0,1,1,1,1,1]`
`target := 0`, overshoot to index `3`. After finding the boundary at index `2`, we can remember that there are at least 2 instances of `1`, _even before we set it as our target_, just because we happen to visit it while searching for `0`

If you only want to track one bystander at a time, your aux-mem will be `O(1)`. But my plan is to remember _all bystanders_, so I need something like a hash-map. I'm not sure if it's worth it, as maps have overhead

### Radix-tree
By treating the list as a "flattened" `N`-ary tree (such as a [BST](https://en.wikipedia.org/wiki/Binary_search_tree)), there's no need for partitions to be unique! However, this requires partitions to be ordered in such a way that bisections never mistakenly believe that a parent node only contains occurrences of the same value.

To understand why, here's how this alt differs:
1. If the 1st and last values of this section of the list are the same, assume all values in-between are the same; if not, continue
2. Bisect this section and perform step#1 on each side

If there's even a single different value in a "blind spot", the result could be wildly incorrect!

I still don't know how to describe the requirement, but I believe it's practical to satisfy.

BTW, if the flat-tree is a [heap](https://en.wikipedia.org/wiki/Binary_heap#Heap_implementation) ([_ahnentafel_](https://en.wikipedia.org/wiki/Ahnentafel) if you will), then [it'd be cache-optimal](https://curiouscoding.nl/posts/static-search-tree)! See also [this HN comment](https://news.ycombinator.com/item?id=42563407)
