# Mere equivalences of group actions

<pre class="Agda"><a id="47" class="Keyword">module</a> <a id="54" href="group-theory.mere-equivalences-group-actions.html" class="Module">group-theory.mere-equivalences-group-actions</a> <a id="99" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="155" class="Keyword">open</a> <a id="160" class="Keyword">import</a> <a id="167" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="group-theory.equivalences-group-actions.html" class="Module">group-theory.equivalences-group-actions</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="group-theory.group-actions.html" class="Module">group-theory.group-actions</a>
<a id="371" class="Keyword">open</a> <a id="376" class="Keyword">import</a> <a id="383" href="group-theory.groups.html" class="Module">group-theory.groups</a>
</pre>
</details>

## Idea

A **mere equivalence** of [group actions](group-theory.group-actions.md) is an
element of the
[propositional truncation](foundation.propositional-truncations.md) of the type
of [equivalences of group actions](group-theory.equivalences-group-actions.md).

## Definition

<pre class="Agda"><a id="707" class="Keyword">module</a> <a id="714" href="group-theory.mere-equivalences-group-actions.html#714" class="Module">_</a>
  <a id="718" class="Symbol">{</a><a id="719" href="group-theory.mere-equivalences-group-actions.html#719" class="Bound">l1</a> <a id="722" href="group-theory.mere-equivalences-group-actions.html#722" class="Bound">l2</a> <a id="725" href="group-theory.mere-equivalences-group-actions.html#725" class="Bound">l3</a> <a id="728" class="Symbol">:</a> <a id="730" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="735" class="Symbol">}</a> <a id="737" class="Symbol">(</a><a id="738" href="group-theory.mere-equivalences-group-actions.html#738" class="Bound">G</a> <a id="740" class="Symbol">:</a> <a id="742" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="748" href="group-theory.mere-equivalences-group-actions.html#719" class="Bound">l1</a><a id="750" class="Symbol">)</a>
  <a id="754" class="Symbol">(</a><a id="755" href="group-theory.mere-equivalences-group-actions.html#755" class="Bound">X</a> <a id="757" class="Symbol">:</a> <a id="759" href="group-theory.group-actions.html#1098" class="Function">action-Group</a> <a id="772" href="group-theory.mere-equivalences-group-actions.html#738" class="Bound">G</a> <a id="774" href="group-theory.mere-equivalences-group-actions.html#722" class="Bound">l2</a><a id="776" class="Symbol">)</a> <a id="778" class="Symbol">(</a><a id="779" href="group-theory.mere-equivalences-group-actions.html#779" class="Bound">Y</a> <a id="781" class="Symbol">:</a> <a id="783" href="group-theory.group-actions.html#1098" class="Function">action-Group</a> <a id="796" href="group-theory.mere-equivalences-group-actions.html#738" class="Bound">G</a> <a id="798" href="group-theory.mere-equivalences-group-actions.html#725" class="Bound">l3</a><a id="800" class="Symbol">)</a>
  <a id="804" class="Keyword">where</a>

  <a id="813" href="group-theory.mere-equivalences-group-actions.html#813" class="Function">mere-equiv-prop-action-Group</a> <a id="842" class="Symbol">:</a> <a id="844" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="849" class="Symbol">(</a><a id="850" href="group-theory.mere-equivalences-group-actions.html#719" class="Bound">l1</a> <a id="853" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="855" href="group-theory.mere-equivalences-group-actions.html#722" class="Bound">l2</a> <a id="858" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="860" href="group-theory.mere-equivalences-group-actions.html#725" class="Bound">l3</a><a id="862" class="Symbol">)</a>
  <a id="866" href="group-theory.mere-equivalences-group-actions.html#813" class="Function">mere-equiv-prop-action-Group</a> <a id="895" class="Symbol">=</a> <a id="897" href="foundation.propositional-truncations.html#2109" class="Function">trunc-Prop</a> <a id="908" class="Symbol">(</a><a id="909" href="group-theory.equivalences-group-actions.html#1794" class="Function">equiv-action-Group</a> <a id="928" href="group-theory.mere-equivalences-group-actions.html#738" class="Bound">G</a> <a id="930" href="group-theory.mere-equivalences-group-actions.html#755" class="Bound">X</a> <a id="932" href="group-theory.mere-equivalences-group-actions.html#779" class="Bound">Y</a><a id="933" class="Symbol">)</a>

  <a id="938" href="group-theory.mere-equivalences-group-actions.html#938" class="Function">mere-equiv-action-Group</a> <a id="962" class="Symbol">:</a> <a id="964" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="967" class="Symbol">(</a><a id="968" href="group-theory.mere-equivalences-group-actions.html#719" class="Bound">l1</a> <a id="971" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="973" href="group-theory.mere-equivalences-group-actions.html#722" class="Bound">l2</a> <a id="976" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="978" href="group-theory.mere-equivalences-group-actions.html#725" class="Bound">l3</a><a id="980" class="Symbol">)</a>
  <a id="984" href="group-theory.mere-equivalences-group-actions.html#938" class="Function">mere-equiv-action-Group</a> <a id="1008" class="Symbol">=</a> <a id="1010" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1020" href="group-theory.mere-equivalences-group-actions.html#813" class="Function">mere-equiv-prop-action-Group</a>
</pre>