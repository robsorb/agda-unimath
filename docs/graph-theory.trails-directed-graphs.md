# Trails in directed graphs

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="graph-theory.trails-directed-graphs.html" class="Module">graph-theory.trails-directed-graphs</a> <a id="81" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="137" class="Keyword">open</a> <a id="142" class="Keyword">import</a> <a id="149" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="graph-theory.walks-directed-graphs.html" class="Module">graph-theory.walks-directed-graphs</a>
</pre>
</details>

## Idea

A **trail** in a [directed graph](graph-theory.directed-graphs.md) is a
[walk](graph-theory.walks-directed-graphs.md) that goes through each edge at
most once.

<pre class="Agda"><a id="542" class="Keyword">module</a> <a id="549" href="graph-theory.trails-directed-graphs.html#549" class="Module">_</a>
  <a id="553" class="Symbol">{</a><a id="554" href="graph-theory.trails-directed-graphs.html#554" class="Bound">l1</a> <a id="557" href="graph-theory.trails-directed-graphs.html#557" class="Bound">l2</a> <a id="560" class="Symbol">:</a> <a id="562" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="567" class="Symbol">}</a> <a id="569" class="Symbol">(</a><a id="570" href="graph-theory.trails-directed-graphs.html#570" class="Bound">G</a> <a id="572" class="Symbol">:</a> <a id="574" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="589" href="graph-theory.trails-directed-graphs.html#554" class="Bound">l1</a> <a id="592" href="graph-theory.trails-directed-graphs.html#557" class="Bound">l2</a><a id="594" class="Symbol">)</a>
  <a id="598" class="Keyword">where</a>

  <a id="607" href="graph-theory.trails-directed-graphs.html#607" class="Function">is-trail-walk-Directed-Graph</a> <a id="636" class="Symbol">:</a>
    <a id="642" class="Symbol">{</a><a id="643" href="graph-theory.trails-directed-graphs.html#643" class="Bound">x</a> <a id="645" href="graph-theory.trails-directed-graphs.html#645" class="Bound">y</a> <a id="647" class="Symbol">:</a> <a id="649" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="671" href="graph-theory.trails-directed-graphs.html#570" class="Bound">G</a><a id="672" class="Symbol">}</a> <a id="674" class="Symbol">→</a> <a id="676" href="graph-theory.walks-directed-graphs.html#1683" class="Datatype">walk-Directed-Graph</a> <a id="696" href="graph-theory.trails-directed-graphs.html#570" class="Bound">G</a> <a id="698" href="graph-theory.trails-directed-graphs.html#643" class="Bound">x</a> <a id="700" href="graph-theory.trails-directed-graphs.html#645" class="Bound">y</a> <a id="702" class="Symbol">→</a> <a id="704" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="707" class="Symbol">(</a><a id="708" href="graph-theory.trails-directed-graphs.html#554" class="Bound">l1</a> <a id="711" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="713" href="graph-theory.trails-directed-graphs.html#557" class="Bound">l2</a><a id="715" class="Symbol">)</a>
  <a id="719" href="graph-theory.trails-directed-graphs.html#607" class="Function">is-trail-walk-Directed-Graph</a> <a id="748" href="graph-theory.trails-directed-graphs.html#748" class="Bound">w</a> <a id="750" class="Symbol">=</a>
    <a id="756" href="foundation-core.injective-maps.html#1182" class="Function">is-injective</a> <a id="769" class="Symbol">(</a><a id="770" href="graph-theory.walks-directed-graphs.html#18363" class="Function">total-edge-edge-on-walk-Directed-Graph</a> <a id="809" href="graph-theory.trails-directed-graphs.html#570" class="Bound">G</a> <a id="811" href="graph-theory.trails-directed-graphs.html#748" class="Bound">w</a><a id="812" class="Symbol">)</a>

  <a id="817" href="graph-theory.trails-directed-graphs.html#817" class="Function">trail-Directed-Graph</a> <a id="838" class="Symbol">:</a> <a id="840" class="Symbol">(</a><a id="841" href="graph-theory.trails-directed-graphs.html#841" class="Bound">x</a> <a id="843" href="graph-theory.trails-directed-graphs.html#843" class="Bound">y</a> <a id="845" class="Symbol">:</a> <a id="847" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="869" href="graph-theory.trails-directed-graphs.html#570" class="Bound">G</a><a id="870" class="Symbol">)</a> <a id="872" class="Symbol">→</a> <a id="874" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="877" class="Symbol">(</a><a id="878" href="graph-theory.trails-directed-graphs.html#554" class="Bound">l1</a> <a id="881" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="883" href="graph-theory.trails-directed-graphs.html#557" class="Bound">l2</a><a id="885" class="Symbol">)</a>
  <a id="889" href="graph-theory.trails-directed-graphs.html#817" class="Function">trail-Directed-Graph</a> <a id="910" href="graph-theory.trails-directed-graphs.html#910" class="Bound">x</a> <a id="912" href="graph-theory.trails-directed-graphs.html#912" class="Bound">y</a> <a id="914" class="Symbol">=</a>
    <a id="920" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="922" class="Symbol">(</a><a id="923" href="graph-theory.walks-directed-graphs.html#1683" class="Datatype">walk-Directed-Graph</a> <a id="943" href="graph-theory.trails-directed-graphs.html#570" class="Bound">G</a> <a id="945" href="graph-theory.trails-directed-graphs.html#910" class="Bound">x</a> <a id="947" href="graph-theory.trails-directed-graphs.html#912" class="Bound">y</a><a id="948" class="Symbol">)</a> <a id="950" class="Symbol">(</a><a id="951" href="graph-theory.trails-directed-graphs.html#607" class="Function">is-trail-walk-Directed-Graph</a><a id="979" class="Symbol">)</a>

  <a id="984" href="graph-theory.trails-directed-graphs.html#984" class="Function">walk-trail-Directed-Graph</a> <a id="1010" class="Symbol">:</a>
    <a id="1016" class="Symbol">{</a><a id="1017" href="graph-theory.trails-directed-graphs.html#1017" class="Bound">x</a> <a id="1019" href="graph-theory.trails-directed-graphs.html#1019" class="Bound">y</a> <a id="1021" class="Symbol">:</a> <a id="1023" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1045" href="graph-theory.trails-directed-graphs.html#570" class="Bound">G</a><a id="1046" class="Symbol">}</a> <a id="1048" class="Symbol">→</a>
    <a id="1054" href="graph-theory.trails-directed-graphs.html#817" class="Function">trail-Directed-Graph</a> <a id="1075" href="graph-theory.trails-directed-graphs.html#1017" class="Bound">x</a> <a id="1077" href="graph-theory.trails-directed-graphs.html#1019" class="Bound">y</a> <a id="1079" class="Symbol">→</a> <a id="1081" href="graph-theory.walks-directed-graphs.html#1683" class="Datatype">walk-Directed-Graph</a> <a id="1101" href="graph-theory.trails-directed-graphs.html#570" class="Bound">G</a> <a id="1103" href="graph-theory.trails-directed-graphs.html#1017" class="Bound">x</a> <a id="1105" href="graph-theory.trails-directed-graphs.html#1019" class="Bound">y</a>
  <a id="1109" href="graph-theory.trails-directed-graphs.html#984" class="Function">walk-trail-Directed-Graph</a> <a id="1135" class="Symbol">=</a> <a id="1137" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="1144" href="graph-theory.trails-directed-graphs.html#1144" class="Function">is-trail-trail-Directed-Graph</a> <a id="1174" class="Symbol">:</a>
    <a id="1180" class="Symbol">{</a><a id="1181" href="graph-theory.trails-directed-graphs.html#1181" class="Bound">x</a> <a id="1183" href="graph-theory.trails-directed-graphs.html#1183" class="Bound">y</a> <a id="1185" class="Symbol">:</a> <a id="1187" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1209" href="graph-theory.trails-directed-graphs.html#570" class="Bound">G</a><a id="1210" class="Symbol">}</a> <a id="1212" class="Symbol">(</a><a id="1213" href="graph-theory.trails-directed-graphs.html#1213" class="Bound">t</a> <a id="1215" class="Symbol">:</a> <a id="1217" href="graph-theory.trails-directed-graphs.html#817" class="Function">trail-Directed-Graph</a> <a id="1238" href="graph-theory.trails-directed-graphs.html#1181" class="Bound">x</a> <a id="1240" href="graph-theory.trails-directed-graphs.html#1183" class="Bound">y</a><a id="1241" class="Symbol">)</a> <a id="1243" class="Symbol">→</a>
    <a id="1249" href="graph-theory.trails-directed-graphs.html#607" class="Function">is-trail-walk-Directed-Graph</a> <a id="1278" class="Symbol">(</a><a id="1279" href="graph-theory.trails-directed-graphs.html#984" class="Function">walk-trail-Directed-Graph</a> <a id="1305" href="graph-theory.trails-directed-graphs.html#1213" class="Bound">t</a><a id="1306" class="Symbol">)</a>
  <a id="1310" href="graph-theory.trails-directed-graphs.html#1144" class="Function">is-trail-trail-Directed-Graph</a> <a id="1340" class="Symbol">=</a> <a id="1342" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>
## External links

- [Path (graph theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>) at
  Wikipedia
- [Trail](https://www.wikidata.org/entity/Q17455228) on Wikidata
- [Trail](https://mathworld.wolfram.com/Trail.html) at Wolfram MathWorld
