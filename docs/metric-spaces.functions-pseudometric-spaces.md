# Functions between pseudometric spaces

<pre class="Agda"><a id="50" class="Keyword">module</a> <a id="57" href="metric-spaces.functions-pseudometric-spaces.html" class="Module">metric-spaces.functions-pseudometric-spaces</a> <a id="101" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="157" class="Keyword">open</a> <a id="162" class="Keyword">import</a> <a id="169" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="195" class="Keyword">open</a> <a id="200" class="Keyword">import</a> <a id="207" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="metric-spaces.pseudometric-spaces.html" class="Module">metric-spaces.pseudometric-spaces</a>
</pre>
</details>

## Idea

{{#concept "Functions" Disambiguation="between pseudometric spaces" Agda=type-function-Pseudometric-Space}}
between [pseudometric spaces](metric-spaces.pseudometric-spaces.md) are
functions between their carrier types.

## Definitions

### The type of functions between pseudometric spaces

<pre class="Agda"><a id="606" class="Keyword">module</a> <a id="613" href="metric-spaces.functions-pseudometric-spaces.html#613" class="Module">_</a>
  <a id="617" class="Symbol">{</a><a id="618" href="metric-spaces.functions-pseudometric-spaces.html#618" class="Bound">lx</a> <a id="621" href="metric-spaces.functions-pseudometric-spaces.html#621" class="Bound">lx&#39;</a> <a id="625" href="metric-spaces.functions-pseudometric-spaces.html#625" class="Bound">ly</a> <a id="628" href="metric-spaces.functions-pseudometric-spaces.html#628" class="Bound">ly&#39;</a> <a id="632" class="Symbol">:</a> <a id="634" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="639" class="Symbol">}</a>
  <a id="643" class="Symbol">(</a><a id="644" href="metric-spaces.functions-pseudometric-spaces.html#644" class="Bound">X</a> <a id="646" class="Symbol">:</a> <a id="648" href="metric-spaces.pseudometric-spaces.html#5387" class="Function">Pseudometric-Space</a> <a id="667" href="metric-spaces.functions-pseudometric-spaces.html#618" class="Bound">lx</a> <a id="670" href="metric-spaces.functions-pseudometric-spaces.html#621" class="Bound">lx&#39;</a><a id="673" class="Symbol">)</a> <a id="675" class="Symbol">(</a><a id="676" href="metric-spaces.functions-pseudometric-spaces.html#676" class="Bound">Y</a> <a id="678" class="Symbol">:</a> <a id="680" href="metric-spaces.pseudometric-spaces.html#5387" class="Function">Pseudometric-Space</a> <a id="699" href="metric-spaces.functions-pseudometric-spaces.html#625" class="Bound">ly</a> <a id="702" href="metric-spaces.functions-pseudometric-spaces.html#628" class="Bound">ly&#39;</a><a id="705" class="Symbol">)</a>
  <a id="709" class="Keyword">where</a>

  <a id="718" href="metric-spaces.functions-pseudometric-spaces.html#718" class="Function">type-function-Pseudometric-Space</a> <a id="751" class="Symbol">:</a> <a id="753" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="756" class="Symbol">(</a><a id="757" href="metric-spaces.functions-pseudometric-spaces.html#618" class="Bound">lx</a> <a id="760" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="762" href="metric-spaces.functions-pseudometric-spaces.html#625" class="Bound">ly</a><a id="764" class="Symbol">)</a>
  <a id="768" href="metric-spaces.functions-pseudometric-spaces.html#718" class="Function">type-function-Pseudometric-Space</a> <a id="801" class="Symbol">=</a>
    <a id="807" href="metric-spaces.pseudometric-spaces.html#5584" class="Function">type-Pseudometric-Space</a> <a id="831" href="metric-spaces.functions-pseudometric-spaces.html#644" class="Bound">X</a> <a id="833" class="Symbol">→</a> <a id="835" href="metric-spaces.pseudometric-spaces.html#5584" class="Function">type-Pseudometric-Space</a> <a id="859" href="metric-spaces.functions-pseudometric-spaces.html#676" class="Bound">Y</a>
</pre>
### The identity function on a pseudometric space

<pre class="Agda"><a id="925" class="Keyword">module</a> <a id="932" href="metric-spaces.functions-pseudometric-spaces.html#932" class="Module">_</a>
  <a id="936" class="Symbol">{</a><a id="937" href="metric-spaces.functions-pseudometric-spaces.html#937" class="Bound">l1</a> <a id="940" href="metric-spaces.functions-pseudometric-spaces.html#940" class="Bound">l2</a> <a id="943" class="Symbol">:</a> <a id="945" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="950" class="Symbol">}</a> <a id="952" class="Symbol">(</a><a id="953" href="metric-spaces.functions-pseudometric-spaces.html#953" class="Bound">M</a> <a id="955" class="Symbol">:</a> <a id="957" href="metric-spaces.pseudometric-spaces.html#5387" class="Function">Pseudometric-Space</a> <a id="976" href="metric-spaces.functions-pseudometric-spaces.html#937" class="Bound">l1</a> <a id="979" href="metric-spaces.functions-pseudometric-spaces.html#940" class="Bound">l2</a><a id="981" class="Symbol">)</a>
  <a id="985" class="Keyword">where</a>

  <a id="994" href="metric-spaces.functions-pseudometric-spaces.html#994" class="Function">id-Pseudometric-Space</a> <a id="1016" class="Symbol">:</a> <a id="1018" href="metric-spaces.functions-pseudometric-spaces.html#718" class="Function">type-function-Pseudometric-Space</a> <a id="1051" href="metric-spaces.functions-pseudometric-spaces.html#953" class="Bound">M</a> <a id="1053" href="metric-spaces.functions-pseudometric-spaces.html#953" class="Bound">M</a>
  <a id="1057" href="metric-spaces.functions-pseudometric-spaces.html#994" class="Function">id-Pseudometric-Space</a> <a id="1079" class="Symbol">=</a> <a id="1081" href="foundation-core.function-types.html#307" class="Function">id</a>
</pre>