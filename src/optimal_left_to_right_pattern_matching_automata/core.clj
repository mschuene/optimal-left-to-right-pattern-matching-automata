(ns optimal-left-to-right-pattern-matching-automata.core
  (:require [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.zip :as zip]))

(def omega '?)

(defn matching-item
  "A matching item is a triple r:a*b where ab is a term and r is a rule label.
   The label identifies the origin of the term ab and hence, in a term rewriting system, the rewrite rule which has to be applied when ab is matched * is called
  the matching dot, a the prefix and b the suffix. The first symbol of b is the matching symbol. The position of the matching dot is the matching position"
  [r a b]
  [r a b])

(defn matching-symbol [matching-item]
  (let [[r a b] matching-item]
    (first b)))

(def infinity (Double/MAX_VALUE))

(defn final? [matching-item]
  (let [[r a b] matching-item]
    (empty? b)))

(defn matching-position [matching-item]
  (if (final? matching-item)
    infinity
    (let [[r a b] matching-item]
      (inc (count a)))))
(defn initial-matching-item [label pattern]
  [label '() pattern])

(defn matching-set? [matching-items]
  (let [[r a b] (first matching-items)]
    (every? #(let [[r2 a2 b2] %] (= r r2)) (rest matching-items))))

(defn initial-matching-set? [matching-items]
  (and (matching-set? matching-items) (= '() (second (first matching-items)))))

(defn final-matching-set? [matching-items]
  (and (matching-set? matching-items) (= '() (nth (first matching-items) 2))))

(defn forward-matching-position [matching-item]
  (let [[r a b] matching-item]
    [r (concat a [(first b)]) (rest b)]))

(defn functions [matching-set]
  (into #{} (filter #(or (and (symbol? %) (not= omega %))
                         (and (sequential? %)
                              (symbol? (first %))
                              (number? (second %))))
                    (map matching-symbol matching-set))))

(defn arity [function-symbol]
  (or (and (sequential? function-symbol) (second function-symbol)) 0))

(defn accept [matching-items s]
  (map forward-matching-position
       (filter #(= (matching-symbol %) s) matching-items)))

(defn close [matching-items]
  (let [F (functions matching-items)]
    (set/union matching-items
               (for [matching-item matching-items
                     function-symbol F
                     :let [arityf (arity function-symbol)]
                     :when (and (= omega (matching-symbol matching-item)))]
                 (let [[r a b] matching-item]
                   [r a (concat [function-symbol] (repeat arityf omega)
                                (rest b))])))))

(defn delta [matching-items s]
  (close (accept matching-items s)))

;;quick and dirty functional graph implementation
(def empty-graph {})

(defn add-node [g n]
  (if (g n)
    g
    (assoc g n {:next #{} :prev #{}})))

(defn add-edge [g n1 n2 l]
  (-> g
      (add-node n1)
      (add-node n2)
      (update-in [n1 :next] conj [n2 l])
      (update-in [n2 :prev] conj [n1 l])))

(defn remove-edge [g n1 n2 l]
  (-> g
      (add-node n1)
      (add-node n2)
      (update-in [n1 :next] disj [n2 l])
      (update-in [n2 :prev] disj [n1 l])))

(defn remove-node [g n]
  (if-let [{:keys [next prev]} (g n)]
    ((comp
      #(dissoc % n)
      #(reduce (fn [g* [n* l*]] (remove-edge g* n* n l*)) % prev)
      #(reduce (fn [g* [n* l*]] (remove-edge g* n n* l*)) % next))
     g)
    g))

(defn equivalent-matching-items? [matching-item1 matching-item2]
  (let [[r1 a1 b1] matching-item1 [r2 a2 b2] matching-item2]
    (and (= r1 r2) (= b1 b2))))

(defn extract-first-by
  "returns [extracted rest-of-collection] or false"
  [f coll]
  (loop [[c & cs] coll rest-coll []]
    (if c
      (if (f c)
        [c (concat rest-coll cs)]
        (recur cs (conj rest-coll c)))
      false)))

(defn equivalent-matching-sets? [matching-set1 matching-set2]
  (loop [[mit & mits] matching-set1 matching-set2 matching-set2]
    (if mit
      (if-let [[mit2 mits2] (extract-first-by #(equivalent-matching-items? mit %)
                                              matching-set2)]
        (recur mits mits2)
        false)
      (empty? matching-set2))))

(defn failure? [state]
  (or (= '() state) (nil? state)))

(defn get-next-node [g n l]
  (some #(and (= (second %) l) (first %)) (get-in g [n :next])))

(defn search-equivalent-node [graph node]
  (first (for [[n v] graph
               :when (equivalent-matching-sets? node n)]
           n)))

(defn insert-according-to-matching-position [nodes-to-visit new-matching-set]
  ;;nodes-to-visit has to be sorted according to matching-position
  ;;all matching positions in a matching set are the same
  (let [nmp (matching-position (first new-matching-set))]
    (loop [[n & ns :as nodes-left] nodes-to-visit new-nodes-to-visit []]
      (if n
        (if (<= (matching-position (first n)) nmp)
          (recur ns (conj new-nodes-to-visit n))
          (vec (concat new-nodes-to-visit [new-matching-set] nodes-left)))
        (conj nodes-to-visit new-matching-set)))))

;;problem hier? gibt nur ein omega jetzt mehrere
(defn create-new-states [pos nodes-to-visit graph]
  (let [current-state (nth nodes-to-visit pos)
        F (functions current-state)]
    (loop [[s & ss] (concat F [omega]) nodes-to-visit nodes-to-visit graph graph]
      (if s
        ;;work to do
        (let [new-matching-set (delta current-state s)]
          ;;check if there is already an equivalent matching-set in the graph
          (if-let [eq-node (search-equivalent-node graph new-matching-set)]
            (recur ss nodes-to-visit (add-edge graph current-state eq-node s))
            (recur ss (insert-according-to-matching-position
                       nodes-to-visit new-matching-set)
                   (add-edge graph current-state new-matching-set s))))
        ;;all symbols consumpted, so return the new state
        [graph nodes-to-visit]))))

(defn create-dag [initial-matching-set]
  (loop [graph empty-graph nodes-to-visit [initial-matching-set] pos 0]
    (if (= (count nodes-to-visit) pos)
      ;;all nodes visited, so return graph
      (remove-node graph '())
      (let [[new-graph new-nodes-to-visit]
            (create-new-states pos nodes-to-visit graph)]
        (recur new-graph new-nodes-to-visit (inc pos))))))

(defn consume-next [g current-state symbol]
  (let [next-state (get-next-node g current-state symbol)]
    (if (failure? next-state)
      ;;there was no link, so go through omega link
      [(get-next-node g current-state omega) [symbol]]
      [next-state []])))

(defn consume-next-level-down [g current-state [symbol count]]
  (let [next-state (get-next-node g current-state [symbol count])]
    (if (failure? next-state)
      ;;there was no link, so go through omega link
      [(get-next-node g current-state [omega count]) [symbol]]
      [next-state []])))


(defn- next-without-down
  [loc]
  (if (= :end (loc 1))
    loc
    (or
     (zip/right loc)
     (loop [p loc]
       (if (zip/up p)
         (or (zip/right (zip/up p)) (recur (zip/up p)))
         [(zip/node p) :end])))))

(defn match-expression [g patterns expression]
  (loop [loc (zip/seq-zip expression) node patterns bindings []]
    (if (or (failure? node) (zip/end? loc))
      ;;done
      [node bindings]
      (if (zip/branch? loc)
        ;;ok try if head symbol matches
        ;;we are using preorder throughout matching
        (let [children-count (dec (count (zip/children loc)))
              head-loc (zip/next loc)
              [next-node add-bindings]
              (consume-next-level-down g node [(first head-loc) children-count])]
          (if (failure? next-node)
            ;;head got no match so we have to stay at the original level and try
            ;;to match there for a value or omega
            (let [[next-node add-bindings] (consume-next g node (first loc))]   
              (recur (next-without-down loc) next-node
                     (concat bindings add-bindings)))
            ;;head location got a match so we go on on this level
            (recur (zip/next head-loc) next-node
                   (concat bindings add-bindings))))
        ;;we have no possibility to go down a level deeper so we can just
        ;;consume directly
        (let [[next-node add-bindings] (consume-next g node (first loc))]
          (recur (zip/next loc) next-node
                 (concat bindings add-bindings)))))))

(use 'clojure.test)
(let [initial-matching-set (close [(initial-matching-item 1 '([? 2] a b))
                                   (initial-matching-item 2 '([? 1] a))
                                   (initial-matching-item 3 '(?))])
      dag (create-dag initial-matching-set)]
  (is (= '[([3 (?) ()]) (1)] (match-expression dag initial-matching-set 1)))
  (is (= '[([3 ([? 1] a) ()] [2 ([? 1] a) ()]) (+)]
         (match-expression dag initial-matching-set '(+ a))))
  (is (= '[([3 ([? 2] a b) ()] [1 ([? 2] a b) ()]) (+)]
         (match-expression dag initial-matching-set '(+ a b))))
  (is (= '[([3 (?) ()]) ((+ a b c))]
         (match-expression dag initial-matching-set '(+ a b c)))))

(defn get-in-expression [expression key]
  (loop [loc (zip/seq-zip expression) [k & ks] key]
    (if k
      (let [new-loc (loop [k k loc (zip/down loc)]
                      (if (> k 0)
                        (recur (dec k) (zip/right loc))
                        loc))]
        (recur new-loc ks))
      (first loc))))

(defn compile-step [g current-state rule-map]
  (let [possible-moves (doall (map last (:next (get g current-state))))
        head-moves (doall (filter sequential? possible-moves))
        current-level-moves (doall (remove sequential? possible-moves))]
    (if (empty? possible-moves) 
      `(and (zip/end? ~'loc)
            ;;current-state was successfully matched. Now get the results for the
            ;;matched rules in current-stater
            (or
             ~@(for [[label & rest] (sort-by first (filter final? current-state))
                     :let [[conditions result omga-positions]
                           (get rule-map label)]]
                 `(let [~@(for [[name pos] omga-positions
                                entry
                                [name `(get-in-expression ~'expression ~pos)]]
                            entry)]
                    (and ~@(concat conditions [result]))))))
      `(or ~(if (empty? head-moves)
              'false
              ;;have to test going a level deeper
              `(and (zip/branch? ~'loc)
                    (let [~'head-loc (zip/next ~'loc)]
                      (case (first ~'head-loc)
                        ;;now all next steps have to be written down in a
                        ;;case - the right hand side will be a recursive
                        ;;call to create the code at the next level
                        ;;the default of case is either nil or the level
                        ;;from following a [? <number>] label in the graph
                        ~@(concat
                           (for [[s c] head-moves :when (not= omega s)
                                 entry
                                 [s `(and
                                      (= (dec (count (zip/children ~'loc))) ~c)
                                      (let [~'loc (zip/next ~'head-loc)]
                                        ~(compile-step
                                          g
                                          (get-next-node
                                           g current-state [s c])
                                          rule-map)))]]
                             entry)
                           [(let [omega-downs (filter #(= (first %) omega)
                                                      head-moves)]
                              `(case (dec (count (zip/children ~'loc)))
                                 ~@(concat
                                    (for [[omga c] omega-downs
                                          entry
                                          [c
                                           `(let [~'loc (zip/next ~'head-loc)]
                                              ~(compile-step
                                                g
                                                (get-next-node
                                                 g current-state[omega c])
                                                rule-map))]]
                                      entry)
                                    ;;no further defaulting possible - fail
                                    '(nil))))])))))
           (case (first ~'loc)
             ~@(concat
                (for [symbol current-level-moves :when (not= omega symbol)
                      entry
                      [symbol `(let [~'loc (next-without-down ~'loc)]
                                 ~(compile-step
                                   g
                                   (get-next-node g current-state symbol)
                                   rule-map))]]
                  entry)
                [(if (some #{omega} current-level-moves)
                   ;;we have a default case to fall back to
                   `(let [~'loc (next-without-down ~'loc)]
                      ~(compile-step
                        g
                        (get-next-node g current-state omega)
                        rule-map))
                   'nil)]))))))



(defn compile-rules [rules]
  (let [res
        (for [[label pattern conditions result omga-positions] rules]
          [(initial-matching-item label pattern) [label [conditions result
                                                         omga-positions]]])
        initial-matching-set (close (map first res))
        rule-map (into {} (map second res))
        dag (create-dag initial-matching-set)]
    `(fn [~'expression]
       (let [~'loc (zip/seq-zip ~'expression)]
         ~(compile-step dag initial-matching-set rule-map)))))

(let [rules
      [[1 '([f 4] a a ? a) [] '?a '{?a [3]}]
       [2 '([f 4] [g 2] a ? a ? a) '[(= ?a ?b)] '?b '{?b [1 2] ?a [3]}]]
      f (eval (compile-rules rules))]
  (is (= 'c (f '(f (g a c) a c a))))
  (is (not (f '(f (g a b) a c a))))
  (is (= 'a (f '(f a a a a))))
  (is (not (f '(f a a a b)))))
