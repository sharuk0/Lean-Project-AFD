##📄 README: Verificación del Lema de Bombeo (Pumping Lemma) para Lenguajes Regulares en Lean 4Este proyecto en Lean 4 formaliza la definición de **Autómatas Finitos Deterministas (DFA)** y el concepto de **Lenguajes Regulares**. Culmina con la prueba formal del **Lema de Bombeo para Lenguajes Regulares**, una herramienta fundamental en la teoría de lenguajes formales.

El código utiliza el principio del palomar (Pigeonhole Principle) disponible en la biblioteca `Mathlib` para establecer la propiedad de "bombeo" de las cadenas en lenguajes regulares.

---

###🚀 Estructuras y Definiciones Clave####1. Autómata Finito Determinista (`DFA`)La estructura `DFA` se define sobre un alfabeto genérico `sigma` y consta de:

* `Q`: El tipo de los estados, que debe ser un tipo finito (`Fintype`).
* `δ`: La función de transición (`Q → sigma → Q`).
* `q0`: El estado inicial.
* `F`: El conjunto de estados de aceptación.

```lean
structure DFA (sigma : Type u) where
    Q : Type u
    [fintype_Q : Fintype Q]
    δ : Q → sigma → Q
    q0 : Q
    F : Set Q

```

####2. Función de Transición Extendida y Aceptación* **`DFA.step` (\delta^*)**: La función de transición extendida que lleva un estado inicial y una lista de símbolos (palabra) a un estado final.
* Definición: `def step : M.Q → List sigma → M.Q`


* **`DFA.accepts`**: Predicado que verifica si un DFA acepta una palabra.
* Definición: `def accepts (w : List sigma) : Prop := step M M.q0 w ∈ M.F`


* **`DFA.language`**: El conjunto de todas las palabras aceptadas por el DFA.
* Definición: `def language : Set (List sigma) := { w | M.accepts w }`



####3. Lenguajes Regulares* **`RegularLanguage`**: Un predicado que es verdadero si un lenguaje puede ser reconocido por algún DFA.
* Definición: `def RegularLanguage (sigma : Type) (L : Language sigma) : Prop := ∃ M : DFA sigma, L = M.language`



---

###🔑 Teoremas Principales (Formalización de la Prueba)La demostración del Lema de Bombeo se construye a partir de varios lemas intermedios:

####1. `pigeonhole_states`Este lema aplica el **Principio del Palomar**. Si una palabra w es suficientemente larga (su longitud es mayor o igual al número de estados del DFA, p = |\text{M.Q}| ), entonces el camino de estados que recorre la palabra debe tener un ciclo.

* **Resultado:** Garantiza que existen dos prefijos de la palabra, w_{\text{take } j} y w_{\text{take } l} con j < l \le p, que terminan en el mismo estado:



####2. `cycle_property`Formaliza la consecuencia del palomar: si un prefijo x y un prefijo más largo xy llevan al mismo estado, entonces el subsegmento y (la "bomba") es un ciclo desde y hacia ese estado.

* **Resultado:**



donde x = w_{\text{take } j} y y = w_{\text{drop } j \text{ take } (l-j)}.

####3. `pumping_preserves_acceptance`Demuestra que si una palabra w=xyz es aceptada y y es un ciclo (es decir, \delta^*(\delta^*(q_0, x), y) = \delta^*(q_0, x)), entonces cualquier número de repeticiones de y (la palabra \mathbf{x y^i z}) también será aceptado.

####4. `pumping_lemma`Une todos los lemas anteriores para establecer el Lema de Bombeo formal:

**Teorema (Pumping Lemma):**

Si L es un Lenguaje Regular, entonces existe un número p (la longitud de bombeo, que es |\text{M.Q}|) tal que cualquier palabra w \in L con |w| \ge p se puede descomponer en w = xyz, cumpliendo las siguientes tres condiciones:

1. y \ne [] (La sección a bombear no es vacía).
2. |xy| \le p (La bomba se encuentra en los primeros p caracteres).
3. \forall i \in \mathbb{N}, x y^i z \in L (Cualquier número de repeticiones de y mantiene la palabra en el lenguaje).

---

###🧪 Uso Futuro (Ejemplo Comentado)La sección final del código proporciona un esqueleto para utilizar el `pumping_lemma` en una prueba por contradicción, típicamente usada para demostrar que un lenguaje *no es* regular (por ejemplo, el lenguaje \{a^n b^n \mid n \ge 0\}).

