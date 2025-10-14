# Terminal spans on families of types

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="foundation.terminal-spans-families-of-types.html" class="Module">foundation.terminal-spans-families-of-types</a> <a id="99" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="155" class="Keyword">open</a> <a id="160" class="Keyword">import</a> <a id="167" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.morphisms-spans-families-of-types.html" class="Module">foundation.morphisms-spans-families-of-types</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="foundation.spans-families-of-types.html" class="Module">foundation.spans-families-of-types</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A [span](foundation.spans-families-of-types.md) `𝒮` on a family of types
`A : I → 𝒰` is said to be
{{#concept "terminal" Disambiguation="span on a family of types" Agda=is-terminal-span-type-family}}
if for each span `𝒯` on `A` the type of
[morphisms of spans](foundation.morphisms-spans-families-of-types.md) `𝒯 → 𝒮` is
[contractible](foundation-core.contractible-types.md).

## Definitions

### The predicate of being a terminal span on a family of types

<pre class="Agda"><a id="832" class="Keyword">module</a> <a id="839" href="foundation.terminal-spans-families-of-types.html#839" class="Module">_</a>
  <a id="843" class="Symbol">{</a><a id="844" href="foundation.terminal-spans-families-of-types.html#844" class="Bound">l1</a> <a id="847" href="foundation.terminal-spans-families-of-types.html#847" class="Bound">l2</a> <a id="850" href="foundation.terminal-spans-families-of-types.html#850" class="Bound">l3</a> <a id="853" class="Symbol">:</a> <a id="855" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="860" class="Symbol">}</a> <a id="862" class="Symbol">{</a><a id="863" href="foundation.terminal-spans-families-of-types.html#863" class="Bound">I</a> <a id="865" class="Symbol">:</a> <a id="867" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="870" href="foundation.terminal-spans-families-of-types.html#844" class="Bound">l1</a><a id="872" class="Symbol">}</a> <a id="874" class="Symbol">{</a><a id="875" href="foundation.terminal-spans-families-of-types.html#875" class="Bound">A</a> <a id="877" class="Symbol">:</a> <a id="879" href="foundation.terminal-spans-families-of-types.html#863" class="Bound">I</a> <a id="881" class="Symbol">→</a> <a id="883" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="886" href="foundation.terminal-spans-families-of-types.html#847" class="Bound">l2</a><a id="888" class="Symbol">}</a> <a id="890" class="Symbol">(</a><a id="891" href="foundation.terminal-spans-families-of-types.html#891" class="Bound">𝒮</a> <a id="893" class="Symbol">:</a> <a id="895" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="912" href="foundation.terminal-spans-families-of-types.html#850" class="Bound">l3</a> <a id="915" href="foundation.terminal-spans-families-of-types.html#875" class="Bound">A</a><a id="916" class="Symbol">)</a>
  <a id="920" class="Keyword">where</a>

  <a id="929" href="foundation.terminal-spans-families-of-types.html#929" class="Function">is-terminal-span-type-family</a> <a id="958" class="Symbol">:</a> <a id="960" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="966" href="foundation.terminal-spans-families-of-types.html#929" class="Function">is-terminal-span-type-family</a> <a id="995" class="Symbol">=</a>
    <a id="1001" class="Symbol">{</a><a id="1002" href="foundation.terminal-spans-families-of-types.html#1002" class="Bound">l</a> <a id="1004" class="Symbol">:</a> <a id="1006" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1011" class="Symbol">}</a> <a id="1013" class="Symbol">(</a><a id="1014" href="foundation.terminal-spans-families-of-types.html#1014" class="Bound">𝒯</a> <a id="1016" class="Symbol">:</a> <a id="1018" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="1035" href="foundation.terminal-spans-families-of-types.html#1002" class="Bound">l</a> <a id="1037" href="foundation.terminal-spans-families-of-types.html#875" class="Bound">A</a><a id="1038" class="Symbol">)</a> <a id="1040" class="Symbol">→</a>
    <a id="1046" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="1055" class="Symbol">(</a><a id="1056" href="foundation.morphisms-spans-families-of-types.html#1587" class="Function">hom-span-type-family</a> <a id="1077" href="foundation.terminal-spans-families-of-types.html#1014" class="Bound">𝒯</a> <a id="1079" href="foundation.terminal-spans-families-of-types.html#891" class="Bound">𝒮</a><a id="1080" class="Symbol">)</a>
</pre>
## See also

- [The universal property of dependent function types](foundation.universal-property-dependent-function-types.md)
  is equivalent to the condition of being a terminal span of families of types.
