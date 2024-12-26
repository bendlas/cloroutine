(ns ^:no-doc cloroutine.impl
  (:refer-clojure :exclude [compile])
  (:require #?(:cljs [cloroutine.impl.analyze-cljs :as impl]
               :clj  [cloroutine.impl.analyze-clj  :as impl]))
  #?(:cljs (:require-macros [cloroutine.impl :refer [safe hint]])
     :clj  (:import (clojure.lang IObj)
                    (java.lang.reflect Field Modifier)
                    (sun.misc Unsafe))))

(defmacro spy
  ([form]
   `(spy ~(pr-str form) ~form))
  ([tag form]
   `(let [res# ~form]
      (println ~tag "=>" (pr-str res#))
      res#)))


(def unsafe
  #?(:clj
     (some (fn [^Field f]
             (when (Modifier/isStatic (.getModifiers f))
               (when (= Unsafe (.getType f))
                 (.setAccessible f true)
                 (.get f nil))))
           (.getDeclaredFields Unsafe))
     :default nil))

(def box->prim
  '{java.lang.Boolean   boolean
    java.lang.Byte      byte
    java.lang.Character char
    java.lang.Short     short
    java.lang.Integer   int
    java.lang.Long      long
    java.lang.Float     float
    java.lang.Double    double})

(def prim->box
  (reduce-kv #(assoc %1 %3 %2) {} box->prim))

(defn with-tag [form tag]
  (if #?(:clj (instance? IObj form) :cljs (satisfies? IMeta form))
    (with-meta form (assoc (meta form) :tag tag)) form))

(defn var-name [ast]
  (when (= :var (:op ast))
    (or (when-some [v (:info ast)]
          (:name v))
        (when-some [v (:meta ast)]
          (symbol (str (:ns v)) (name (:name v)))))))

(defmacro hint [to from form]
  (if (:js-globals &env)
    (with-tag form to)
    (if (prim->box to)
      (list to form)
      (if-some [from-box (prim->box from)]
        (with-tag (list (symbol (str from-box "/valueOf")) form) to)
        (with-tag form to)))))

(defmacro safe [[error success] failure & finally]
  `(try ~success
        (catch ~(if (:js-globals &env) :default `Throwable) ~error ~failure)
        ~@(when finally (list `(finally ~@finally)))))

(defn coroutine [^objects state]
  (fn
    ([]
     (let [result ((aget state 0) state)]
       (if (identical? result state)
         (recur) result)))
    ([f] (f (coroutine (aclone state))))
    ([f a] (f (coroutine (aclone state)) a))
    ([f a b] (f (coroutine (aclone state)) a b))
    ([f a b c] (f (coroutine (aclone state)) a b c))
    ([f a b c & ds] (apply f (coroutine (aclone state)) a b c ds))))

(defn sym [& args]
  (symbol (apply str (interpose "-" args))))

(def conj-vec (fnil conj []))
(def conj-set (fnil conj #{}))
(def into-set (fnil into #{}))

(defn- cljs-provided? []
  #?(:cljs true
     :clj  (boolean (requiring-resolve 'cljs.env/default-compiler-env))))

(defn analyze [env form]
  (if (and (:js-globals env) (cljs-provided?))
    #?(:cljs (impl/analyze env form)
       :clj  ((requiring-resolve 'cloroutine.impl.analyze-cljs/analyze) env form))
    #?(:cljs (throw (ex-info "Can't target JVM from clojurescript." {}))
       :clj  (impl/analyze env form))))

(defn coerce-js-literal-key [k]
  (or
    (and (string? k) k)
    (and (keyword? k) (nil? (namespace k)) (name k))
    (throw (ex-info (str "Invalid JS literal key - " k) {:key k}))))

;; === SSA helpers

(defn emit-apply [args meta & prefixes]
  (with-meta `(~@prefixes ~@args) meta))

(defn emit-member-access [[inst & args] meta member]
  (with-meta `(. ~inst ~member ~@args) meta))

(defn emit-member-assign [[inst val] meta member]
  (with-meta `(set! (. ~inst ~member) ~val) meta))

(defn emit-case [[test default & thens] meta tests]
  (with-meta `(case ~test ~@(interleave tests thens) ~default) meta))

(defn emit-vec [args meta]
  (with-meta (vec args) meta))

(defn emit-set [args meta]
  (with-meta (set args) meta))

(defn emit-map [args meta]
  (with-meta (apply hash-map args) meta))

(defn emit-js-object [args meta keys]
  (with-meta (cons 'cljs.core/js-obj (interleave keys args)) meta))

(defn emit-js-array [args meta]
  (with-meta (cons 'cljs.core/array args) meta))

(defn emit-place [ssa tag place]
  (spy :emit-place [ssa tag place])
  (if (:skip-place ssa)
    place
    `(hint ~tag ~(-> ssa :places place :tag) ~place)))

(defn instance [ast]
  (or (:instance ast) (:target ast)))

(defn field [ast]
  (symbol (str "-" (or (:field ast) (:m-or-f ast)))))

(defn case-tests [{:keys [tests nodes]}]
  (if tests
    (map (comp list :form) tests)
    (map (comp (partial map :form) :tests) nodes)))

(defn case-thens [{:keys [thens nodes]}]
  (if thens
    (map :then thens)
    (map (comp :then :then) nodes)))

(defn try-handler [ast sym]
  (if (:name ast)
    (:catch ast)
    ((fn rec [catch catches]
       (if-some [[{{class :val} :class :keys [local body]} & catches] catches]
         (let [then {:op       :let
                     :bindings [(assoc local :init {:op :local :name sym})]
                     :body     body}]
           (case class
             java.lang.Throwable then
             {:op   :if
              :test {:op     :instance?
                     :class  class
                     :target {:op :local :name sym}}
              :then then
              :else (rec catch catches)}))
         catch))
     {:op :throw
      :exception {:op :local :name sym}}
     (seq (:catches ast)))))

(defn constructor [{:keys [class]}]
  (or (:val class) (:name class)))

(defn ast-meta [ast]
  (select-keys (:env ast) [:file :column :line]))

(defn class->symbol [c]
  #?(:clj
     (when (instance? Class c)
       (let [s (symbol (.getName ^Class c))]
         (get box->prim s s)))))

(defn tag->symbol [c]
  (or
   (when (symbol? c) c)
   (class->symbol c)))

(defn function [ast]
  (or (:f ast) (:fn ast)))

(defn js-template [ast]
  (or (:code ast) (apply str (interpose "~{}" (:segs ast)))))

(defn restore [m p & ks]
  (reduce (fn [m k]
            (if-some [x (p k)]
              (assoc m k x)
              (dissoc m k))) m ks))

(defn current-block [ssa]
  (sym (:prefix ssa) 'block (-> ssa :blocks count dec)))

(defn with-place [ssa place]
  (spy :with-place [ssa place])
  (let [block (current-block ssa)]
    (if #_(or (:skip-place ssa)
              (= block (-> ssa :places place :block)))
        (= block (-> ssa :places (get place) :block))
        ssa (update-in ssa [:blocks block :read] conj-set place))))

(defn collect [ssa rf asts f & args]
  (loop [ssa (assoc ssa :result [] :tag [])
         asts (seq asts)]
    (if-some [[ast & asts] asts]
      (let [res (:result ssa)
            tag (:tag ssa)
            ssa (rf ssa ast)]
        (if (contains? ssa :result)
          (recur (-> ssa
                     (update :result (partial conj res))
                     (update :tag (partial conj tag))) asts) ssa))
      (apply f ssa args))))

(declare add-closing)
(defn add-closing-method [ssa {:keys [variadic? params body]}]
  (-> ssa
      (update :shadow into-set (map :name) params)
      (add-closing body)
      (restore ssa :shadow)
      (update :result (partial list (if variadic?
                                      (-> (into [] (map :name) (pop params))
                                          (conj '& (-> params peek :name)))
                                      (into [] (map :name) params))))))

(defn add-closing [ssa ast]
  (let [met (ast-meta ast)]
    (case (:op ast)

      :with-meta
      (let [ssa (add-closing ssa (:expr ast))]
        (update ssa :result (partial list `with-meta) (:form (:meta ast))))

      (:const :var :js-var :quote :the-var :static-field)
      (assoc ssa :result (:form ast))

      :local
      (let [l (:name ast)
            s (get-in ssa [:shadow l])
            p (get-in ssa [:locals l])]
        (spy :add-closing-local [:local ssa l s p])
        (if s
          (assoc ssa :result `(hint ~(-> ast :tag tag->symbol) ~(:tag met) ~s))
          (if p
            (-> ssa
                (with-place p)
                (assoc :result (emit-place ssa (:tag met) p)))
            (assoc ssa :result `(hint ~(-> ast :tag tag->symbol) ~(:tag met) ~l)))))

      (:let :loop)
      (let [previous ssa
            {:keys [op bindings body]} ast
            {:as ssa bindings :result}
            (reduce (fn [{:as ssa bindings :result} {:keys [name init]}]
                      (let [{:as ssa init :result} (add-closing ssa init)]
                        (-> ssa
                            (assoc :result (conj bindings name init))
                            (update :shadow conj-set name))))
                    (assoc ssa :result []) bindings)
            {:as ssa body :result}
            (add-closing ssa body)]
        (-> ssa
            (restore previous :shadow)
            (assoc :result (emit-apply [bindings body] met (case op :let `let* :loop `loop*)))))

      (:invoke :prim-invoke)
      (collect ssa add-closing (cons (function ast) (:args ast)) update :result emit-apply met)

      :keyword-invoke
      (collect ssa add-closing (list (:target ast)) update :result emit-apply met (-> ast :keyword :form))

      :protocol-invoke
      (collect ssa add-closing (list* (:protocol-fn ast) (:target ast) (:args ast)) update :result emit-apply met)

      :instance?
      (collect ssa add-closing (list (:target ast)) update :result emit-apply met `instance? (:class ast))

      (:instance-call :host-call)
      (collect ssa add-closing (cons (instance ast) (:args ast)) update :result emit-member-access met (:method ast))

      (:instance-field :host-field :host-interop)
      (collect ssa add-closing (cons (instance ast) (:args ast)) update :result emit-member-access met (field ast))

      :static-call
      (collect ssa add-closing (:args ast) update :result emit-apply met '. (:class ast) (:method ast))

      :new
      (collect ssa add-closing (:args ast) update :result emit-apply met 'new (constructor ast))

      :set!
      (collect ssa add-closing [(:target ast) (:val ast)] update :result emit-apply met `set!)

      :def
      (collect ssa add-closing (list (:init ast)) update :result emit-apply met `def (-> ast :var :form))

      :js
      (collect ssa add-closing (:args ast) update :result emit-apply met 'js* (js-template ast))

      :js-array
      (collect ssa add-closing (:items ast) update :result emit-js-array met)

      :js-object
      (collect ssa add-closing (:vals ast) update :result emit-js-object met (map coerce-js-literal-key (:keys ast)))

      :vector
      (collect ssa add-closing (:items ast) update :result emit-vec met)

      :set
      (collect ssa add-closing (:items ast) update :result emit-set met)

      :map
      (collect ssa add-closing (interleave (:keys ast) (:vals ast)) update :result emit-map met)

      :recur
      (collect ssa add-closing (:exprs ast) update :result emit-apply met `recur)

      :do
      (collect ssa add-closing (conj (vec (:statements ast)) (:ret ast)) update :result emit-apply met `do)

      :if
      (collect ssa add-closing [(:test ast) (:then ast) (:else ast)] update :result emit-apply met `if)

      :case
      (collect ssa add-closing (list* (:test ast) (:default ast) (case-thens ast))
               update :result emit-case met (case-tests ast))

      :throw
      (collect ssa add-closing (list (:exception ast)) update :result emit-apply met `throw)

      :monitor-enter
      (collect ssa add-closing (list (:target ast)) update :result emit-apply met 'monitor-enter)

      :monitor-exit
      (collect ssa add-closing (list (:target ast)) update :result emit-apply met 'monitor-exit)

      :fn
      (let [local (:local ast)
            cljs-crap (when-some [t (-> ast :methods first :type)] {:cljs.analyzer/type t})]
        (-> (reduce (fn [ssa method]
                      (-> ssa
                          (add-closing-method method)
                          (update :result (partial conj-vec (:result ssa)))))
                    (-> (if local (update ssa :shadow conj-set (:name local)) ssa)
                        (dissoc :result)) (:methods ast))
            (restore ssa :shadow)
            (update :result (if local (partial cons (:name local)) identity))
            (update :result emit-apply (merge met cljs-crap) 'fn*)))

      :reify
      (-> (reduce (fn [ssa method]
                    (-> ssa
                        (add-closing-method (update method :params (partial into [(:this method)])))
                        (update :result (partial cons (:name method)))
                        (update :result (partial conj (:result ssa)))))
                  (assoc ssa :result []) (:methods ast))
          (update :result (->> (-> (:interfaces ast) #?(:clj (disj IObj)))
                               (map tag->symbol)
                               (apply partial list* `reify))))

      :deftype
      (let [{:keys [t fields pmasks protocols body]} ast]
        (-> ssa
            (update :shadow into-set fields)
            (add-closing body)
            (restore ssa :shadow)
            (update :result (partial list `deftype* (vary-meta t assoc :protocols protocols) fields pmasks))))

      :letfn
      (let [prev ssa
            {:keys [bindings body]} ast
            {:as ssa bindings :result}
            (reduce (fn [{:as ssa bindings :result} {:keys [init name]}]
                      (-> ssa
                          (add-closing (dissoc init :local))
                          (update :result with-meta nil)
                          (update :result (partial conj-vec bindings name))))
                    (-> ssa
                        (assoc :result [])
                        (update :shadow into-set (map :name) bindings)) bindings)]
        (-> ssa
            (add-closing body)
            (restore prev :shadow)
            (update :result list)
            (update :result emit-apply met 'letfn* bindings)))

      :try
      (let [handled (or (:name ast) (sym (:prefix ssa) 'exception))
            {:as ssa body :result} (add-closing ssa (:body ast))
            {:as ssa handler :result} (-> ssa
                                          (update :shadow conj-set handled)
                                          (add-closing (try-handler ast handled))
                                          (restore ssa :shadow))
            {:as ssa finally :result} (if-some [ast (:finally ast)]
                                        (add-closing ssa ast)
                                        (dissoc ssa :result))]
        (assoc ssa :result (with-meta `(safe [~handled ~body] ~handler ~@(when finally (list finally))) met))))))

(defn add-block [ssa]
  (let [block (sym (:prefix ssa) 'block (-> ssa :blocks count))]
    (-> ssa
        (update :blocks assoc block {})
        (update :caught conj-set block))))

(defn add-place
  ([ssa init] (add-place ssa init nil))
  ([{:as ssa :keys [prefix places]} init tag]
   (spy :add-place [ssa init tag])
   (if (:skip-place ssa)
     (assoc ssa :result init)
     (let [block (current-block ssa)
           place (sym prefix 'place (count places))]
       (-> ssa
           (assoc :result place :tag tag)
           (assoc-in [:places place] {:init init :tag tag :block block})
           (update-in [:blocks block :bind] conj-vec place))))))

(defn with-transition [ssa origin target write state & path]
  (-> ssa
      (assoc-in (into [:blocks origin] path) {:block target :write write :state state})
      (update-in [:blocks target :origins] conj-set origin)))

(defn with-resume [ssa origin state]
  (with-transition ssa origin (current-block ssa) {} state :default))

(defn with-clause-jump [ssa origin value]
  (with-transition ssa origin (current-block ssa) {}
    (sym (:prefix ssa) 'state) :clauses value))

(defn with-default-jump [ssa origin]
  (with-transition ssa origin (current-block ssa) {}
    (sym (:prefix ssa) 'state) :default))

(defn with-continue [ssa origin write]
  (with-transition ssa origin (current-block ssa) write
    (sym (:prefix ssa) 'state) :default))

(defn with-joins [ssa target branches]
  (reduce-kv (fn [ssa block place]
               (with-continue ssa block {target place}))
             ssa branches))

(defn with-test [ssa test]
  (update-in ssa [:blocks (current-block ssa)] assoc :test test))

(defn with-handler [{:as ssa :keys [prefix]} caught write]
  (reduce (fn [ssa block]
            (with-transition ssa block (current-block ssa) write
              (sym prefix 'state) :handler))
          ssa caught))

(defn add-many [ssa tag f & args]
  (-> (reduce with-place ssa (:result ssa))
      (add-place `(hint ~tag nil ~(apply f (map (partial emit-place ssa) (:tag ssa) (:result ssa)) args)) tag)))

(defn add-break [ssa suspend resume]
  (-> (reduce with-place ssa (:result ssa))
      (add-block)
      (with-resume (current-block ssa) (cons suspend (:result ssa)))
      (add-place (list resume))))

(defn add-recur [{:as ssa :keys [prefix] [block & targets] :loop places :result}]
  (-> (reduce with-place ssa (:result ssa))
      (with-transition (current-block ssa) block
        (zipmap targets places)
        (sym prefix 'state) :default)
      (dissoc :result)))

(declare add-breaking)
(defn add-bindings [previous bindings f & args]
  (loop [ssa previous
         bindings (seq bindings)
         places []]
    (if-some [[{:keys [name init]} & bindings] bindings]
      (as-> ssa ssa
        (add-breaking ssa init)
        (update ssa :locals assoc name (:result ssa))
        (if-some [place (:result ssa)]
          (recur ssa bindings (conj places place)) ssa))
      (as-> ssa ssa
        (assoc ssa :result places)
        (apply f ssa args)
        (restore ssa previous :locals)))))

(defn add-loop-body [previous body]
  (as-> previous ssa
    (-> ssa
        (add-block)
        (with-default-jump (current-block ssa)))
    (-> ssa
        (assoc :loop (cons (current-block ssa) (:result ssa)))
        (add-breaking body))
    (restore ssa previous :loop)))

(defn add-branch [ssa ast]
  (let [prv (:result ssa)
        ssa (add-breaking ssa ast)]
    (if-some [place (:result ssa)]
      (-> ssa
          (with-place place)
          (assoc :result (assoc prv (current-block ssa) place)))
      (assoc ssa :result prv))))

(defn add-conditional [ssa test clauses default]
  (let [ssa (add-breaking ssa test)
        block (current-block ssa)]
    (if-some [place (:result ssa)]
      (let [{:as ssa target :result}
            (-> ssa
                (with-place place)
                (with-test place)
                (add-place nil))
            {:as ssa branches :result}
            (-> (reduce-kv (fn [ssa test then]
                             (-> ssa
                                 (add-block)
                                 (with-clause-jump block test)
                                 (add-branch then)))
                           (dissoc ssa :result) clauses)
                (add-block)
                (with-default-jump block)
                (add-branch default))]
        (if branches
          (-> ssa
              (add-block)
              (with-joins target branches)
              (with-place target)
              (assoc :result target))
          (dissoc ssa :result))) ssa)))

(defn add-breaking [ssa ast]
  (let [tag (-> ast :tag tag->symbol)
        met (ast-meta ast)]
    (case (:op ast)

      :with-meta
      (let [ssa (add-breaking ssa (:expr ast))]
        (update-in ssa [:places (:result ssa) :init] (partial list `with-meta) (:form (:meta ast))))

      :local
      (if-some [place (get-in ssa [:locals (:name ast)])]
        (-> ssa
            (with-place place)
            (add-place (emit-place ssa tag place) tag))
        (add-place ssa (:form ast) tag))

      (:const :var :js-var :quote :the-var :static-field)
      #_(add-place ssa `(hint ~tag ~(-> ast :o-tag tag->symbol) ~(:form ast)) tag)
      (assoc (spy ssa)
             :result (:form ast)
             :skip-place true)

      (:fn :reify :deftype)
      (let [ssa (add-closing ssa ast)]
        (add-place ssa (:result ssa) tag))

      (:invoke :prim-invoke)
      (if-some [[suspend resume] (find (:breaks ssa) (-> ast function var-name))]
        (collect ssa add-breaking (:args ast) add-break suspend resume)
        (collect ssa add-breaking (cons (function ast) (:args ast)) add-many tag emit-apply met))

      :keyword-invoke
      (collect ssa add-breaking (list (:target ast)) add-many tag emit-apply met (-> ast :keyword :form))

      :protocol-invoke
      (collect ssa add-breaking (list* (:protocol-fn ast) (:target ast) (:args ast)) add-many tag emit-apply met)

      :instance?
      (collect ssa add-breaking (list (:target ast)) add-many tag emit-apply met `instance? (:class ast))

      (:instance-call :host-call)
      (collect ssa add-breaking (cons (instance ast) (:args ast)) add-many tag emit-member-access met (:method ast))

      (:instance-field :host-field :host-interop)
      (collect ssa add-breaking (cons (instance ast) (:args ast)) add-many tag emit-member-access met (field ast))

      :static-call
      (collect ssa add-breaking (:args ast) add-many tag emit-apply met '. (:class ast) (:method ast))

      :new
      (collect ssa add-breaking (:args ast) add-many tag emit-apply met 'new (constructor ast))

      :set!
      (let [{:keys [target val]} ast]
        (case (:op target)
          :var (collect ssa add-breaking [val] add-many tag emit-apply met `set! (:form target))
          (:instance-field :host-field :host-interop)
          (collect ssa add-breaking (list (instance target) val) add-many tag emit-member-assign met (field target))))

      :def
      (collect ssa add-breaking (list (:init ast)) add-many tag emit-apply met `def (with-meta (:name ast) (:val (:meta ast))))

      :js
      (collect ssa add-breaking (:args ast) add-many tag emit-apply met 'js* (js-template ast))

      :js-array
      (collect ssa add-breaking (:items ast) add-many tag emit-js-array met)

      :js-object
      (collect ssa add-breaking (:vals ast) add-many tag emit-js-object met (map coerce-js-literal-key (:keys ast)))

      :vector
      (collect ssa add-breaking (:items ast) add-many tag emit-vec met)

      :set
      (collect ssa add-breaking (:items ast) add-many tag emit-set met)

      :map
      (collect ssa add-breaking (interleave (:keys ast) (:vals ast)) add-many tag emit-map met)

      :let
      (add-bindings ssa (:bindings ast) add-breaking (:body ast))

      :loop
      (add-bindings ssa (:bindings ast) add-loop-body (:body ast))

      :recur
      (collect ssa add-breaking (:exprs ast) add-recur)

      :do
      (collect ssa add-breaking (:statements ast) add-breaking (:ret ast))

      :case
      (add-conditional ssa (:test ast) (zipmap (case-tests ast) (case-thens ast)) (:default ast))

      :if
      (add-conditional ssa (:test ast) {'(nil false) (:else ast)} (:then ast))

      :try
      (let [caught  (:caught ssa)
            handled (or (:name ast) (sym (:prefix ssa) 'exception))
            {:as ssa target :result} (add-place ssa nil)
            {:as ssa status :result} (add-place ssa false)]
        (-> ssa
            (dissoc :result :caught)
            (add-block)
            (with-default-jump (current-block ssa))
            (add-branch (:body ast))
            (as-> ssa
                (-> ssa
                    (dissoc :caught)
                    (add-block)
                    (with-handler (:caught ssa) {target (sym (:prefix ssa) 'exception)})
                    (update :locals assoc handled target)
                    (add-branch (try-handler ast handled))
                    (restore ssa :locals))
              (-> ssa
                  (assoc :caught caught)
                  (add-block)
                  (with-handler (:caught ssa) {status true target (sym (:prefix ssa) 'exception)})
                  (with-joins target (:result ssa)))
              (if-some [ast (:finally ast)] (add-breaking ssa ast) ssa))
            (with-place target)
            (with-place status)
            (add-place `(if ~status (throw ~target) ~target))))

      :throw
      (-> ssa
          (collect add-breaking [(:exception ast)] add-many tag emit-apply met `throw)
          (dissoc :result))

      :monitor-enter
      (collect ssa add-breaking [(:target ast)] add-many tag emit-apply met '.monitorEnter (with-meta `unsafe `{:tag Unsafe}))

      :monitor-exit
      (collect ssa add-breaking [(:target ast)] add-many tag emit-apply met '.monitorExit (with-meta `unsafe `{:tag Unsafe}))

      :letfn
      (let [prev    ssa
            block   (current-block ssa)
            symbols (map :name (:bindings ast))
            {:as ssa :keys [locals]}
            (reduce (fn [{:as ssa :keys [prefix places]} local]
                      (let [place (sym prefix 'place (count places))]
                        (-> ssa
                            (assoc-in [:locals local] place)
                            (assoc-in [:places place :block] block))))
                    ssa symbols)]
        (-> (reduce (fn [ssa {:keys [name init]}]
                      (let [place (locals name)
                            ssa   (-> ssa
                                      (assoc-in [:locals (-> init :local :name)] place)
                                      (add-closing (dissoc init :local)))]
                        (assoc-in ssa [:places place :init] (with-meta (:result ssa) nil))))
                    ssa (:bindings ast))
            (update-in [:blocks block :bind] conj-vec (map locals symbols))
            (add-breaking (:body ast))
            (restore prev :locals))))))

(defn ssa [ssa ast]
  (as-> (-> ssa (add-block) (add-breaking ast)) ssa
    (if-some [place (:result ssa)]
      (-> ssa
          (with-place place)
          (assoc-in [:blocks (current-block ssa) :default] {:state place})
          (dissoc :result)) ssa)
    (reduce (fn [ssa block]
              (assoc-in ssa [:blocks block :handler]
                        {:state `(throw ~(sym (:prefix ssa) 'exception))}))
            (dissoc ssa :caught) (:caught ssa))))

(def span
  (letfn [(with-overlap [ssa p1 p2]
            (-> ssa
                (update-in [:places p1 :overlaps] conj-set p2)
                (update-in [:places p2 :overlaps] conj-set p1)))
          (backtrack [{:as ssa :keys [places blocks]} block place]
            (let [{:keys [heap origins]} (blocks block)]
              (as-> ssa ssa
                    (update-in ssa [:blocks block :heap] conj-set place)
                    (reduce (fn [ssa overlap] (with-overlap ssa overlap place)) ssa heap)
                    (->> origins
                         (remove (some-fn #{(-> places (get place) :block)} (comp #(get % place) :heap blocks)))
                         (reduce (fn [ssa block] (backtrack ssa block place)) ssa)))))
          (span-block [ssa block {:keys [read]}]
            (reduce (fn [ssa place] (backtrack ssa block place)) ssa read))]
    (fn [{:as ssa :keys [blocks]}]
      (reduce-kv span-block ssa blocks))))

(def color
  (letfn [(color-place [{:as ssa :keys [places]} place]
            (let [color (or (-> places (get place) :color)
                            (->> (range)
                                 (next)
                                 (remove (into #{}
                                               (comp (map (comp :color places)) (remove nil?))
                                               (-> places (get place) :overlaps)))
                                 (first)))]
              (-> ssa
                  (assoc-in [:places place :color] color)
                  (update :colors max color))))]
    (fn [{:as ssa :keys [prefix blocks]}]
      (->> (range (count blocks))
           (mapcat (comp :heap blocks (partial sym prefix 'block)))
           (reduce color-place (assoc ssa :colors 0))))))

(def emit
  (letfn [(emit-state-symbol [ssa]
            (with-meta (sym (:prefix ssa) 'state) {:tag 'objects}))

          (emit-fetch [ssa place]
            (spy :emit-fetch [ssa place])
            (let [{:keys [color tag]} (-> ssa :places (get place))]
              `(hint ~tag nil (aget ~(emit-state-symbol ssa) ~color))))

          (emit-store [ssa [place value]]
            `(aset ~(emit-state-symbol ssa)
                   ~(get-in ssa [:places place :color])
                   ~(when value `(hint nil ~(get-in ssa [:places value :tag]) ~value))))

          (emit-jump [ssa origin {:keys [block write state]}]
            (let [{:keys [heap bind]} (get-in ssa [:blocks origin])
                  needed (get-in ssa [:blocks block :heap] #{})]
              `(do
                 (aset ~(emit-state-symbol ssa) 0 ~block)
                 ~@(map (partial emit-store ssa)
                        (concat (->> (zipmap heap (repeat nil))
                                     (remove (comp needed key)))
                                (->> (merge write (zipmap bind bind))
                                     (filter (comp needed key)))))
                 ~state)))

          (emit-block [{:as ssa :keys [places blocks prefix]} block]
            (let [{:keys [read bind test clauses default handler]} (get blocks block)
                  tests (keys clauses) thens (vals clauses)]
              `(safe [~(sym prefix 'exception)
                      (let [~@(mapcat (juxt identity (partial emit-fetch ssa)) read)]
                        ~((fn rec [bind]
                            (let [[items bind] (split-with symbol? bind)]
                              (if-some [items (seq items)]
                                `(let [~@(interleave items (map (comp :init places) items))]
                                   ~(rec bind))
                                (if-some [[items & bind] (seq bind)]
                                  `(letfn* [~@(interleave items (map (comp :init places) items))]
                                           ~(rec bind))
                                  (case tests
                                    nil (emit-jump ssa block default)
                                    [[nil false]]
                                    `(if ~test
                                       ~(emit-jump ssa block default)
                                       ~(emit-jump ssa block (first thens)))
                                    `(case ~test
                                       ~@(interleave tests (map (partial emit-jump ssa block) thens))
                                       ~(emit-jump ssa block default))))))) bind))]
                 ~(emit-jump ssa block handler))))]
    (fn [{:as ssa :keys [colors blocks prefix]}]
      `(letfn [~@(map (fn [block] (list block [(sym prefix 'state)] (emit-block ssa block))) (keys blocks))]
         (coroutine (doto (object-array ~(inc colors)) (aset 0 ~(sym prefix 'block 0))))))))

(defn compile [prefix breaks env form]
  (-> {:prefix prefix
       :breaks (zipmap (map (comp var-name (partial analyze env)) (keys breaks)) (vals breaks))}
      (ssa (analyze env form))
      (span)
      (color)
      (emit)))
