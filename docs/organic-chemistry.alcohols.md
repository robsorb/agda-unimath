# Alcohols

<pre class="Agda"><a id="21" class="Keyword">module</a> <a id="28" href="organic-chemistry.alcohols.html" class="Module">organic-chemistry.alcohols</a> <a id="55" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="111" class="Keyword">open</a> <a id="116" class="Keyword">import</a> <a id="123" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="276" class="Keyword">open</a> <a id="281" class="Keyword">import</a> <a id="288" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="325" class="Keyword">open</a> <a id="330" class="Keyword">import</a> <a id="337" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>

<a id="404" class="Keyword">open</a> <a id="409" class="Keyword">import</a> <a id="416" href="organic-chemistry.hydrocarbons.html" class="Module">organic-chemistry.hydrocarbons</a>
<a id="447" class="Keyword">open</a> <a id="452" class="Keyword">import</a> <a id="459" href="organic-chemistry.saturated-carbons.html" class="Module">organic-chemistry.saturated-carbons</a>
</pre>
</details>

## Idea

An alcohol is a hydrocarbon with at least one `-OH` group. The type of alcohols
can therefore be defined as the type of hydrocarbons equipped with a
distinguished subset of the available (unbonded) electrons of the carbon atoms.

## Definition

<pre class="Agda"><a id="alcohol"></a><a id="774" href="organic-chemistry.alcohols.html#774" class="Function">alcohol</a> <a id="782" class="Symbol">:</a> <a id="784" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="787" class="Symbol">(</a><a id="788" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="793" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="798" class="Symbol">)</a>
<a id="800" href="organic-chemistry.alcohols.html#774" class="Function">alcohol</a> <a id="808" class="Symbol">=</a>
  <a id="812" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="814" class="Symbol">(</a> <a id="816" href="organic-chemistry.hydrocarbons.html#1569" class="Function">hydrocarbon</a> <a id="828" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="834" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="839" class="Symbol">)</a>
    <a id="845" class="Symbol">(</a> <a id="847" class="Symbol">λ</a> <a id="849" href="organic-chemistry.alcohols.html#849" class="Bound">X</a> <a id="851" class="Symbol">→</a>
      <a id="859" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="861" class="Symbol">(</a> <a id="863" class="Symbol">(</a><a id="864" href="organic-chemistry.alcohols.html#864" class="Bound">c</a> <a id="866" class="Symbol">:</a> <a id="868" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="887" href="organic-chemistry.alcohols.html#849" class="Bound">X</a><a id="888" class="Symbol">)</a> <a id="890" class="Symbol">→</a>
          <a id="902" href="foundation.decidable-subtypes.html#2727" class="Function">decidable-subtype</a> <a id="920" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="926" class="Symbol">(</a><a id="927" href="organic-chemistry.hydrocarbons.html#3894" class="Function">electron-carbon-atom-hydrocarbon</a> <a id="960" href="organic-chemistry.alcohols.html#849" class="Bound">X</a> <a id="962" href="organic-chemistry.alcohols.html#864" class="Bound">c</a><a id="963" class="Symbol">))</a>
        <a id="974" class="Symbol">(</a> <a id="976" class="Symbol">λ</a> <a id="978" href="organic-chemistry.alcohols.html#978" class="Bound">OH</a> <a id="981" class="Symbol">→</a>
          <a id="993" class="Symbol">(</a> <a id="995" class="Symbol">(</a> <a id="997" href="organic-chemistry.alcohols.html#997" class="Bound">c</a> <a id="999" href="organic-chemistry.alcohols.html#999" class="Bound">c&#39;</a> <a id="1002" class="Symbol">:</a> <a id="1004" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="1023" href="organic-chemistry.alcohols.html#849" class="Bound">X</a><a id="1024" class="Symbol">)</a> <a id="1026" class="Symbol">→</a>
            <a id="1040" class="Symbol">(</a> <a id="1042" href="organic-chemistry.alcohols.html#1042" class="Bound">b</a> <a id="1044" class="Symbol">:</a> <a id="1046" href="organic-chemistry.hydrocarbons.html#3426" class="Function">edge-hydrocarbon</a> <a id="1063" href="organic-chemistry.alcohols.html#849" class="Bound">X</a> <a id="1065" class="Symbol">(</a><a id="1066" href="foundation.unordered-pairs.html#4836" class="Function">standard-unordered-pair</a> <a id="1090" href="organic-chemistry.alcohols.html#997" class="Bound">c</a> <a id="1092" href="organic-chemistry.alcohols.html#999" class="Bound">c&#39;</a><a id="1094" class="Symbol">))</a> <a id="1097" class="Symbol">→</a>
            <a id="1111" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="1113" class="Symbol">(</a><a id="1114" href="foundation.decidable-subtypes.html#3255" class="Function">is-in-decidable-subtype</a> <a id="1138" class="Symbol">(</a><a id="1139" href="organic-chemistry.alcohols.html#978" class="Bound">OH</a> <a id="1142" href="organic-chemistry.alcohols.html#997" class="Bound">c</a><a id="1143" class="Symbol">)</a> <a id="1145" class="Symbol">(</a><a id="1146" href="organic-chemistry.hydrocarbons.html#4309" class="Function">bonding-hydrocarbon</a> <a id="1166" href="organic-chemistry.alcohols.html#849" class="Bound">X</a> <a id="1168" href="organic-chemistry.alcohols.html#1042" class="Bound">b</a><a id="1169" class="Symbol">)))</a> <a id="1173" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
          <a id="1185" class="Symbol">(</a> <a id="1187" class="Symbol">(</a> <a id="1189" href="foundation.propositional-truncations.html#1578" class="Function">type-trunc-Prop</a>
            <a id="1217" class="Symbol">(</a> <a id="1219" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1221" class="Symbol">(</a> <a id="1223" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="1242" href="organic-chemistry.alcohols.html#849" class="Bound">X</a><a id="1243" class="Symbol">)</a>
                <a id="1261" class="Symbol">(</a> <a id="1263" class="Symbol">λ</a> <a id="1265" href="organic-chemistry.alcohols.html#1265" class="Bound">c</a> <a id="1267" class="Symbol">→</a> <a id="1269" href="foundation.decidable-subtypes.html#3903" class="Function">type-decidable-subtype</a> <a id="1292" class="Symbol">(</a><a id="1293" href="organic-chemistry.alcohols.html#978" class="Bound">OH</a> <a id="1296" href="organic-chemistry.alcohols.html#1265" class="Bound">c</a><a id="1297" class="Symbol">))))</a> <a id="1302" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
            <a id="1316" class="Symbol">(</a> <a id="1318" class="Symbol">(</a> <a id="1320" href="organic-chemistry.alcohols.html#1320" class="Bound">c</a> <a id="1322" class="Symbol">:</a> <a id="1324" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="1343" href="organic-chemistry.alcohols.html#849" class="Bound">X</a><a id="1344" class="Symbol">)</a> <a id="1346" class="Symbol">→</a>
              <a id="1362" href="foundation.decidable-subtypes.html#3903" class="Function">type-decidable-subtype</a> <a id="1385" class="Symbol">(</a><a id="1386" href="organic-chemistry.alcohols.html#978" class="Bound">OH</a> <a id="1389" href="organic-chemistry.alcohols.html#1320" class="Bound">c</a><a id="1390" class="Symbol">)</a> <a id="1392" class="Symbol">→</a>
              <a id="1408" href="organic-chemistry.saturated-carbons.html#854" class="Function">is-saturated-carbon-hydrocarbon</a> <a id="1440" href="organic-chemistry.alcohols.html#849" class="Bound">X</a> <a id="1442" href="organic-chemistry.alcohols.html#1320" class="Bound">c</a>
              <a id="1458" class="Symbol">))))</a>
</pre>
More explicitly, an alcohol is a hydrocarbon equipped with, for each of its
carbons, a subset of its electrons, where membership in that subset indicates
whether or not a hydroxyl group is bonded to that specific electron. We require
the following conditions:

- The electron shared between a carbon atom and a hydroxyl group can not also be
  shared between that carbon atom and a different carbon.
- There must be at least one hydroxyl group.
- Atoms to which hydroxyl groups are bonded must be saturated.
