# Total partial functions

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="foundation.total-partial-functions.html" class="Module">foundation.total-partial-functions</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.partial-functions.html" class="Module">foundation.partial-functions</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A [partial function](foundation.partial-functions.md) `f : A → B` is said to be
{{#concept "total" Disambiguation="partial function" Agda=is-total-partial-function}}
if the [partial element](foundation.partial-elements.md) `f a` of `B` is defined
for every `a : A`. The type of total partial functions from `A` to `B` is
[equivalent](foundation-core.equivalences.md) to the type of
[functions](foundation-core.function-types.md) from `A` to `B`.

## Definitions

### The predicate of being a total partial function

<pre class="Agda"><a id="850" class="Keyword">module</a> <a id="857" href="foundation.total-partial-functions.html#857" class="Module">_</a>
  <a id="861" class="Symbol">{</a><a id="862" href="foundation.total-partial-functions.html#862" class="Bound">l1</a> <a id="865" href="foundation.total-partial-functions.html#865" class="Bound">l2</a> <a id="868" href="foundation.total-partial-functions.html#868" class="Bound">l3</a> <a id="871" class="Symbol">:</a> <a id="873" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="878" class="Symbol">}</a> <a id="880" class="Symbol">{</a><a id="881" href="foundation.total-partial-functions.html#881" class="Bound">A</a> <a id="883" class="Symbol">:</a> <a id="885" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="888" href="foundation.total-partial-functions.html#862" class="Bound">l1</a><a id="890" class="Symbol">}</a> <a id="892" class="Symbol">{</a><a id="893" href="foundation.total-partial-functions.html#893" class="Bound">B</a> <a id="895" class="Symbol">:</a> <a id="897" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="900" href="foundation.total-partial-functions.html#865" class="Bound">l2</a><a id="902" class="Symbol">}</a> <a id="904" class="Symbol">(</a><a id="905" href="foundation.total-partial-functions.html#905" class="Bound">f</a> <a id="907" class="Symbol">:</a> <a id="909" href="foundation.partial-functions.html#1432" class="Function">partial-function</a> <a id="926" href="foundation.total-partial-functions.html#868" class="Bound">l3</a> <a id="929" href="foundation.total-partial-functions.html#881" class="Bound">A</a> <a id="931" href="foundation.total-partial-functions.html#893" class="Bound">B</a><a id="932" class="Symbol">)</a>
  <a id="936" class="Keyword">where</a>

  <a id="945" href="foundation.total-partial-functions.html#945" class="Function">is-total-prop-partial-function</a> <a id="976" class="Symbol">:</a> <a id="978" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="983" class="Symbol">(</a><a id="984" href="foundation.total-partial-functions.html#862" class="Bound">l1</a> <a id="987" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="989" href="foundation.total-partial-functions.html#868" class="Bound">l3</a><a id="991" class="Symbol">)</a>
  <a id="995" href="foundation.total-partial-functions.html#945" class="Function">is-total-prop-partial-function</a> <a id="1026" class="Symbol">=</a>
    <a id="1032" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1039" href="foundation.total-partial-functions.html#881" class="Bound">A</a> <a id="1041" class="Symbol">(</a><a id="1042" href="foundation.partial-functions.html#2311" class="Function">is-defined-prop-partial-function</a> <a id="1075" href="foundation.total-partial-functions.html#905" class="Bound">f</a><a id="1076" class="Symbol">)</a>

  <a id="1081" href="foundation.total-partial-functions.html#1081" class="Function">is-total-partial-function</a> <a id="1107" class="Symbol">:</a> <a id="1109" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1112" class="Symbol">(</a><a id="1113" href="foundation.total-partial-functions.html#862" class="Bound">l1</a> <a id="1116" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1118" href="foundation.total-partial-functions.html#868" class="Bound">l3</a><a id="1120" class="Symbol">)</a>
  <a id="1124" href="foundation.total-partial-functions.html#1081" class="Function">is-total-partial-function</a> <a id="1150" class="Symbol">=</a> <a id="1152" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1162" href="foundation.total-partial-functions.html#945" class="Function">is-total-prop-partial-function</a>
</pre>
### The type of total partial functions

<pre class="Agda"><a id="total-partial-function"></a><a id="1247" href="foundation.total-partial-functions.html#1247" class="Function">total-partial-function</a> <a id="1270" class="Symbol">:</a>
  <a id="1274" class="Symbol">{</a><a id="1275" href="foundation.total-partial-functions.html#1275" class="Bound">l1</a> <a id="1278" href="foundation.total-partial-functions.html#1278" class="Bound">l2</a> <a id="1281" class="Symbol">:</a> <a id="1283" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1288" class="Symbol">}</a> <a id="1290" class="Symbol">(</a><a id="1291" href="foundation.total-partial-functions.html#1291" class="Bound">l3</a> <a id="1294" class="Symbol">:</a> <a id="1296" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1301" class="Symbol">)</a> <a id="1303" class="Symbol">→</a> <a id="1305" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1308" href="foundation.total-partial-functions.html#1275" class="Bound">l1</a> <a id="1311" class="Symbol">→</a> <a id="1313" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1316" href="foundation.total-partial-functions.html#1278" class="Bound">l2</a> <a id="1319" class="Symbol">→</a> <a id="1321" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1324" class="Symbol">(</a><a id="1325" href="foundation.total-partial-functions.html#1275" class="Bound">l1</a> <a id="1328" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1330" href="foundation.total-partial-functions.html#1278" class="Bound">l2</a> <a id="1333" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1335" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1340" href="foundation.total-partial-functions.html#1291" class="Bound">l3</a><a id="1342" class="Symbol">)</a>
<a id="1344" href="foundation.total-partial-functions.html#1247" class="Function">total-partial-function</a> <a id="1367" href="foundation.total-partial-functions.html#1367" class="Bound">l3</a> <a id="1370" href="foundation.total-partial-functions.html#1370" class="Bound">A</a> <a id="1372" href="foundation.total-partial-functions.html#1372" class="Bound">B</a> <a id="1374" class="Symbol">=</a>
  <a id="1378" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1380" class="Symbol">(</a><a id="1381" href="foundation.partial-functions.html#1432" class="Function">partial-function</a> <a id="1398" href="foundation.total-partial-functions.html#1367" class="Bound">l3</a> <a id="1401" href="foundation.total-partial-functions.html#1370" class="Bound">A</a> <a id="1403" href="foundation.total-partial-functions.html#1372" class="Bound">B</a><a id="1404" class="Symbol">)</a> <a id="1406" href="foundation.total-partial-functions.html#1081" class="Function">is-total-partial-function</a>
</pre>