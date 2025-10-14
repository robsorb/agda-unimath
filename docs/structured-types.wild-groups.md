# Wild groups

<pre class="Agda"><a id="24" class="Keyword">module</a> <a id="31" href="structured-types.wild-groups.html" class="Module">structured-types.wild-groups</a> <a id="60" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="116" class="Keyword">open</a> <a id="121" class="Keyword">import</a> <a id="128" href="foundation.binary-equivalences.html" class="Module">foundation.binary-equivalences</a>
<a id="159" class="Keyword">open</a> <a id="164" class="Keyword">import</a> <a id="171" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="structured-types.wild-monoids.html" class="Module">structured-types.wild-monoids</a>
</pre>
</details>

<pre class="Agda"><a id="is-wild-group-Wild-Monoid"></a><a id="310" href="structured-types.wild-groups.html#310" class="Function">is-wild-group-Wild-Monoid</a> <a id="336" class="Symbol">:</a>
  <a id="340" class="Symbol">{</a><a id="341" href="structured-types.wild-groups.html#341" class="Bound">l</a> <a id="343" class="Symbol">:</a> <a id="345" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="350" class="Symbol">}</a> <a id="352" class="Symbol">(</a><a id="353" href="structured-types.wild-groups.html#353" class="Bound">M</a> <a id="355" class="Symbol">:</a> <a id="357" href="structured-types.wild-monoids.html#3571" class="Function">Wild-Monoid</a> <a id="369" href="structured-types.wild-groups.html#341" class="Bound">l</a><a id="370" class="Symbol">)</a> <a id="372" class="Symbol">→</a> <a id="374" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="377" href="structured-types.wild-groups.html#341" class="Bound">l</a>
<a id="379" href="structured-types.wild-groups.html#310" class="Function">is-wild-group-Wild-Monoid</a> <a id="405" href="structured-types.wild-groups.html#405" class="Bound">M</a> <a id="407" class="Symbol">=</a> <a id="409" href="foundation.binary-equivalences.html#775" class="Function">is-binary-equiv</a> <a id="425" class="Symbol">(</a><a id="426" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="442" href="structured-types.wild-groups.html#405" class="Bound">M</a><a id="443" class="Symbol">)</a>

<a id="Wild-Group"></a><a id="446" href="structured-types.wild-groups.html#446" class="Function">Wild-Group</a> <a id="457" class="Symbol">:</a> <a id="459" class="Symbol">(</a><a id="460" href="structured-types.wild-groups.html#460" class="Bound">l</a> <a id="462" class="Symbol">:</a> <a id="464" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="469" class="Symbol">)</a> <a id="471" class="Symbol">→</a> <a id="473" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="476" class="Symbol">(</a><a id="477" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="482" href="structured-types.wild-groups.html#460" class="Bound">l</a><a id="483" class="Symbol">)</a>
<a id="485" href="structured-types.wild-groups.html#446" class="Function">Wild-Group</a> <a id="496" href="structured-types.wild-groups.html#496" class="Bound">l</a> <a id="498" class="Symbol">=</a> <a id="500" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="502" class="Symbol">(</a><a id="503" href="structured-types.wild-monoids.html#3571" class="Function">Wild-Monoid</a> <a id="515" href="structured-types.wild-groups.html#496" class="Bound">l</a><a id="516" class="Symbol">)</a> <a id="518" href="structured-types.wild-groups.html#310" class="Function">is-wild-group-Wild-Monoid</a>
</pre>