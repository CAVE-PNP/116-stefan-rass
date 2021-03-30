# Claimed Solutions of $`P`$ vs $`NP`$

## The P-versus-NP page

The vast majority of entries are from the `P-versus-NP page`. Here, only the papers that we aim to formalize are listed.

### 49. Zohreh O. Akbari: A polynomial-time algorithm for the maximum clique problem

_See the separate report on [paper #49](../iva_notes/notes_paper49.pdf)_

Claim: $`P = NP`$

Published in: _2013 IEEE/ACIS 12th International Conference on Computer and Information Science (ICIS)_ (see <https://doi.org/10.1109/ICIS.2013.6607889>)

Full text available through Google Scholar.

### 116. Stefan Rass: On the Existence of Weak One-Way Functions

_See the separate report on [paper #116](paper-116.md)_

Claim: $`P ≠ NP`$

Preprint hosted on _arXiv_ (full text available, see <https://arxiv.org/abs/1609.01575>

## More

This is a collection of relevant claimed results found during the work on this project.

### Eric Grigoryan: Linear algorithm for solution n-Queens Completion problem

<!-- Stefan Haan found this entry -->

Claim: $`P = NP`$ (implied)

The n-Queens Completion Problem is an NP-Complete variation of the classic n-Queens Puzzle (see <http://www.claymath.org/events/news/8-queens-puzzle> and [Complexity of n-Queens Completion](https://www.jair.org/index.php/jair/article/download/11079/26262/))

The algorithm is not exact however, as the author notes in ch. 8:

> 1. An algorithm is described which allows solving in linear time the n-Queens Completion problem for an arbitrary composition of k queens, consistently distributed on a chessboard of size $`n×n`$. Moreover, for any composition of $`k`$ queens ($`1 ≤ k < n`$), a solution is provided, if any, or a decision is made that this composition can’t be completed. **The probability of an error in making such a decision does not exceed 0.0001**, and this value decreases with increasing size of a chessboard.

Preprint hosted on _arXiv_ (full text available, see <https://arxiv.org/abs/1912.05935>

Sources available on GitHub: <https://github.com/ericgrig/Completion-n-Queens-Problem>
