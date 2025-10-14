# Abstractions

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="reflection.abstractions.html" class="Module">reflection.abstractions</a> <a id="56" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="112" class="Keyword">open</a> <a id="117" class="Keyword">import</a> <a id="124" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="primitives.strings.html" class="Module">primitives.strings</a>
</pre>
</details>

## Idea

The `Abstraction-Agda` type represents a lambda abstraction.

## Definition

<pre class="Agda"><a id="294" class="Keyword">data</a> <a id="Abstraction-Agda"></a><a id="299" href="reflection.abstractions.html#299" class="Datatype">Abstraction-Agda</a> <a id="316" class="Symbol">{</a><a id="317" href="reflection.abstractions.html#317" class="Bound">l</a> <a id="319" class="Symbol">:</a> <a id="321" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="326" class="Symbol">}</a> <a id="328" class="Symbol">(</a><a id="329" href="reflection.abstractions.html#329" class="Bound">A</a> <a id="331" class="Symbol">:</a> <a id="333" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="336" href="reflection.abstractions.html#317" class="Bound">l</a><a id="337" class="Symbol">)</a> <a id="339" class="Symbol">:</a> <a id="341" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="344" href="reflection.abstractions.html#317" class="Bound">l</a> <a id="346" class="Keyword">where</a>
  <a id="Abstraction-Agda.cons-Abstraction-Agda"></a><a id="354" href="reflection.abstractions.html#354" class="InductiveConstructor">cons-Abstraction-Agda</a> <a id="376" class="Symbol">:</a> <a id="378" href="primitives.strings.html#581" class="Postulate">String</a> <a id="385" class="Symbol">→</a> <a id="387" href="reflection.abstractions.html#329" class="Bound">A</a> <a id="389" class="Symbol">→</a> <a id="391" href="reflection.abstractions.html#299" class="Datatype">Abstraction-Agda</a> <a id="408" href="reflection.abstractions.html#329" class="Bound">A</a>

<a id="411" class="Symbol">{-#</a> <a id="415" class="Keyword">BUILTIN</a> <a id="423" class="Keyword">ABS</a> <a id="427" href="reflection.abstractions.html#299" class="Datatype">Abstraction-Agda</a> <a id="444" class="Symbol">#-}</a>
<a id="448" class="Symbol">{-#</a> <a id="452" class="Keyword">BUILTIN</a> <a id="460" class="Keyword">ABSABS</a> <a id="467" href="reflection.abstractions.html#354" class="InductiveConstructor">cons-Abstraction-Agda</a> <a id="489" class="Symbol">#-}</a>
</pre>