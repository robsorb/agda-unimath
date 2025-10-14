# Integer partitions

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="elementary-number-theory.integer-partitions.html" class="Module">elementary-number-theory.integer-partitions</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda">
</pre>
</details>

## Idea

An integer partition of a natural number n is a list of nonzero natural numbers
that sum up to n, up to reordering. We define the number `p n` of integer
partitions of `n` as the number of connected components in the type of finite
Ferrer diagrams of `Fin n`.
