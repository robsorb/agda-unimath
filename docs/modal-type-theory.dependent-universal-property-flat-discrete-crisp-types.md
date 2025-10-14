# Dependent universal property of flat discrete crisp types

<pre class="Agda"><a id="70" class="Symbol">{-#</a> <a id="74" class="Keyword">OPTIONS</a> <a id="82" class="Pragma">--cohesion</a> <a id="93" class="Pragma">--flat-split</a> <a id="106" class="Symbol">#-}</a>

<a id="111" class="Keyword">module</a> <a id="118" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html" class="Module">modal-type-theory.dependent-universal-property-flat-discrete-crisp-types</a> <a id="191" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="modal-type-theory.flat-modality.html" class="Module">modal-type-theory.flat-modality</a>
</pre>
</details>

## Idea

The
{{#concept "dependent universal property" Disambiguation="of flat discrete crisp types"}}
of a [flat discrete crisp type](modal-type-theory.flat-discrete-crisp-types.md)
`A` states that for any [crisp](modal-type-theory.crisp-types.md) type family
[defined on crisp elements](modal-type-theory.crisp-function-types.md)
`@♭ B : @♭ A → 𝒰`,
[postcomposition](foundation-core.postcomposition-functions.md) by the counit of
the [flat modality](modal-type-theory.flat-modality.md) induces an
[equivalence](foundation-core.equivalences.md) under the flat modality.

## Definitions

### The dependent universal property of flat discrete crisp types

<pre class="Agda"><a id="dependent-coev-flat"></a><a id="1047" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1047" class="Function">dependent-coev-flat</a> <a id="1067" class="Symbol">:</a>
  <a id="1071" class="Symbol">{@</a>♭ <a id="1075" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1075" class="Bound">l1</a> <a id="1078" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1078" class="Bound">l2</a> <a id="1081" class="Symbol">:</a> <a id="1083" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1088" class="Symbol">}</a> <a id="1090" class="Symbol">{@</a>♭ <a id="1094" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1094" class="Bound">A</a> <a id="1096" class="Symbol">:</a> <a id="1098" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1101" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1075" class="Bound">l1</a><a id="1103" class="Symbol">}</a> <a id="1105" class="Symbol">{@</a>♭ <a id="1109" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1109" class="Bound">B</a> <a id="1111" class="Symbol">:</a> <a id="1113" class="Symbol">@</a>♭ <a id="1116" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1094" class="Bound">A</a> <a id="1118" class="Symbol">→</a> <a id="1120" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1123" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1078" class="Bound">l2</a><a id="1125" class="Symbol">}</a> <a id="1127" class="Symbol">→</a>
  <a id="1131" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="1133" class="Symbol">((@</a>♭ <a id="1138" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1138" class="Bound">x</a> <a id="1140" class="Symbol">:</a> <a id="1142" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1094" class="Bound">A</a><a id="1143" class="Symbol">)</a> <a id="1145" class="Symbol">→</a> <a id="1147" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="1149" class="Symbol">(</a><a id="1150" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1109" class="Bound">B</a> <a id="1152" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1138" class="Bound">x</a><a id="1153" class="Symbol">))</a> <a id="1156" class="Symbol">→</a> <a id="1158" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="1160" class="Symbol">((@</a>♭ <a id="1165" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1165" class="Bound">x</a> <a id="1167" class="Symbol">:</a> <a id="1169" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1094" class="Bound">A</a><a id="1170" class="Symbol">)</a> <a id="1172" class="Symbol">→</a> <a id="1174" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1109" class="Bound">B</a> <a id="1176" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1165" class="Bound">x</a><a id="1177" class="Symbol">)</a>
<a id="1179" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1047" class="Function">dependent-coev-flat</a> <a id="1199" class="Symbol">(</a><a id="1200" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="1211" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1211" class="Bound">f</a><a id="1212" class="Symbol">)</a> <a id="1214" class="Symbol">=</a> <a id="1216" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="1227" class="Symbol">(λ</a> <a id="1230" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1230" class="Bound">x</a> <a id="1232" class="Symbol">→</a> <a id="1234" href="modal-type-theory.flat-modality.html#771" class="Function">counit-flat</a> <a id="1246" class="Symbol">(</a><a id="1247" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1211" class="Bound">f</a> <a id="1249" href="modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.html#1230" class="Bound">x</a><a id="1250" class="Symbol">))</a>
</pre>
```text
dependent-universal-property-flat-discrete-crisp-type :
  {@♭ l1 : Level} (@♭ A : UU l1) → UUω
dependent-universal-property-flat-discrete-crisp-type A =
  {@♭ l : Level} {@♭ B : @♭ A → UU l} → is-equiv (dependent-coev-flat {B = B})
```

## Properties

### Flat discrete crisp types satisfy the dependent universal property of flat discrete crisp types

This remains to be formalized.

## See also

- [The universal property of flat discrete crisp types](modal-type-theory.universal-property-flat-discrete-crisp-types.md)

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
