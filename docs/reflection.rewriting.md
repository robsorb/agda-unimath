# Rewriting

<pre class="Agda"><a id="22" class="Symbol">{-#</a> <a id="26" class="Keyword">OPTIONS</a> <a id="34" class="Pragma">--rewriting</a> <a id="46" class="Symbol">#-}</a>

<a id="51" class="Keyword">module</a> <a id="58" href="reflection.rewriting.html" class="Module">reflection.rewriting</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

Agda's rewriting functionality allows us to add new strict equalities to our
type theory. Given an [identification](foundation-core.identity-types.md)
`β : x ＝ y`, then adding a rewrite rule for `β` with

```text
{-# REWRITE β #-}
```

will make it so `x` rewrites to `y`, i.e., `x ≐ y`.

**Warning.** Rewriting is by nature a very unsafe tool so we advice exercising
abundant caution when defining such rules.

## Definitions

We declare to Agda that the
[standard identity relation](foundation.identity-types.md) may be used to define
rewrite rules.

<pre class="Agda"><a id="765" class="Symbol">{-#</a> <a id="769" class="Keyword">BUILTIN</a> <a id="777" class="Keyword">REWRITE</a> <a id="785" href="foundation-core.identity-types.html#2713" class="Function Operator">_＝_</a> <a id="789" class="Symbol">#-}</a>
</pre>
## See also

- [Erasing equality](reflection.erasing-equality.md)

## External links

- [Rewriting](https://agda.readthedocs.io/en/latest/language/rewriting.html) at
  Agda's documentation pages
