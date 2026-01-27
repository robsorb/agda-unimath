# The substitution functor of concrete group actions

<pre class="Agda"><a id="63" class="Keyword">module</a> <a id="70" href="group-theory.substitution-functor-concrete-group-actions.html" class="Module">group-theory.substitution-functor-concrete-group-actions</a> <a id="127" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="312" class="Keyword">open</a> <a id="317" class="Keyword">import</a> <a id="324" href="group-theory.homomorphisms-concrete-groups.html" class="Module">group-theory.homomorphisms-concrete-groups</a>
</pre>
</details>

## Definition

### Substitution of concrete group actions

<pre class="Agda"><a id="451" class="Keyword">module</a> <a id="458" href="group-theory.substitution-functor-concrete-group-actions.html#458" class="Module">_</a>
  <a id="462" class="Symbol">{</a><a id="463" href="group-theory.substitution-functor-concrete-group-actions.html#463" class="Bound">l1</a> <a id="466" href="group-theory.substitution-functor-concrete-group-actions.html#466" class="Bound">l2</a> <a id="469" class="Symbol">:</a> <a id="471" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="476" class="Symbol">}</a> <a id="478" class="Symbol">(</a><a id="479" href="group-theory.substitution-functor-concrete-group-actions.html#479" class="Bound">G</a> <a id="481" class="Symbol">:</a> <a id="483" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="498" href="group-theory.substitution-functor-concrete-group-actions.html#463" class="Bound">l1</a><a id="500" class="Symbol">)</a> <a id="502" class="Symbol">(</a><a id="503" href="group-theory.substitution-functor-concrete-group-actions.html#503" class="Bound">H</a> <a id="505" class="Symbol">:</a> <a id="507" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="522" href="group-theory.substitution-functor-concrete-group-actions.html#466" class="Bound">l2</a><a id="524" class="Symbol">)</a>
  <a id="528" class="Symbol">(</a><a id="529" href="group-theory.substitution-functor-concrete-group-actions.html#529" class="Bound">f</a> <a id="531" class="Symbol">:</a> <a id="533" href="group-theory.homomorphisms-concrete-groups.html#678" class="Function">hom-Concrete-Group</a> <a id="552" href="group-theory.substitution-functor-concrete-group-actions.html#479" class="Bound">G</a> <a id="554" href="group-theory.substitution-functor-concrete-group-actions.html#503" class="Bound">H</a><a id="555" class="Symbol">)</a>
  <a id="559" class="Keyword">where</a>

  <a id="568" href="group-theory.substitution-functor-concrete-group-actions.html#568" class="Function">subst-action-Concrete-Group</a> <a id="596" class="Symbol">:</a>
    <a id="602" class="Symbol">{</a><a id="603" href="group-theory.substitution-functor-concrete-group-actions.html#603" class="Bound">l</a> <a id="605" class="Symbol">:</a> <a id="607" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="612" class="Symbol">}</a> <a id="614" class="Symbol">→</a>
    <a id="620" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="642" href="group-theory.substitution-functor-concrete-group-actions.html#603" class="Bound">l</a> <a id="644" href="group-theory.substitution-functor-concrete-group-actions.html#503" class="Bound">H</a> <a id="646" class="Symbol">→</a> <a id="648" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="670" href="group-theory.substitution-functor-concrete-group-actions.html#603" class="Bound">l</a> <a id="672" href="group-theory.substitution-functor-concrete-group-actions.html#479" class="Bound">G</a>
  <a id="676" href="group-theory.substitution-functor-concrete-group-actions.html#568" class="Function">subst-action-Concrete-Group</a> <a id="704" href="group-theory.substitution-functor-concrete-group-actions.html#704" class="Bound">Y</a> <a id="706" href="group-theory.substitution-functor-concrete-group-actions.html#706" class="Bound">x</a> <a id="708" class="Symbol">=</a>
    <a id="714" href="group-theory.substitution-functor-concrete-group-actions.html#704" class="Bound">Y</a> <a id="716" class="Symbol">(</a><a id="717" href="group-theory.homomorphisms-concrete-groups.html#1274" class="Function">classifying-map-hom-Concrete-Group</a> <a id="752" href="group-theory.substitution-functor-concrete-group-actions.html#479" class="Bound">G</a> <a id="754" href="group-theory.substitution-functor-concrete-group-actions.html#503" class="Bound">H</a> <a id="756" href="group-theory.substitution-functor-concrete-group-actions.html#529" class="Bound">f</a> <a id="758" href="group-theory.substitution-functor-concrete-group-actions.html#706" class="Bound">x</a><a id="759" class="Symbol">)</a>
</pre>