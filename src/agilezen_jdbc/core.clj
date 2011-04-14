(ns agilezen-jdbc.core
  (require [clojure.contrib.sql :as sql]
           [clj-http.client :as http]
           [org.danlarkin.json :as json])
  (:import (java.sql Connection Driver DriverManager
                     PreparedStatement Statement ResultSet
                     ResultSetMetaData)
           (net.sf.jsqlparser.parser CCJSqlParserManager)
           (net.sf.jsqlparser.statement StatementVisitor)
           (net.sf.jsqlparser.statement.select AllColumns PlainSelect
                                               Select SelectVisitor
                                               FromItemVisitor
                                               SelectItemVisitor
                                               SelectExpressionItem
                                               OrderByVisitor
                                               OrderByElement)
           (net.sf.jsqlparser.expression.operators.relational EqualsTo
                                                              NotEqualsTo)
           (net.sf.jsqlparser.expression.operators.conditional AndExpression
                                                               OrExpression)
           (net.sf.jsqlparser.expression LongValue Function NullValue
                                         Parenthesis StringValue
                                         ExpressionVisitor JdbcParameter)
           (net.sf.jsqlparser.schema Column Table)
           (net.sf.jsqlparser.statement.update Update)
           (java.net URLEncoder)))

(def project-list-url "https://agilezen.com/api/v1/projects")

(def story-list-url "https://agilezen.com/api/v1/projects/%s/stories")

(def story-url "https://agilezen.com/api/v1/projects/%s/stories/%s")

(defn project-map [api-key & [filters]]
  (->> (http/get project-list-url
                 {:headers {"X-Zen-ApiKey" api-key}
                  :query-params {"where" filters}})
       :body
       json/decode
       :items
       (map (juxt (comp #(.toLowerCase %) :name) :id))
       (into {})))

(def project-map (memoize project-map))

(defn project-map1 [api-key & [filters]]
  (->> (http/get project-list-url
                 {:headers {"X-Zen-ApiKey" api-key}
                  :query-params {"where" filters}})
       :body
       json/decode
       :items))

(defn project-stories [api-key story-id & [filters]]
  (let [results (->> (http/get (format story-list-url story-id)
                               {:headers {"X-Zen-ApiKey" api-key}
                                :query-params {"pageSize" 1000
                                               "where" filters
                                               "with" "tags,tasks"}})
                     :body
                     json/decode)
        total (:totalItems results)]
    (with-meta
      (->> results
           :items
           (map (fn [item]
                  (-> item
                      (assoc :owner (:userName (:owner item)))
                      (assoc :creator (:userName (:creator item)))
                      (assoc :phase (.toLowerCase (:name (:phase item))))
                      (assoc :project (.toLowerCase (:name (:phase item))))
                      (assoc :tasks (seq (:tasks item)))))))
      {:count total})))

(defn result-set [[fst & rst :as all]]
  (let [fst (or fst {:empty nil})
        all (if (seq all) all [{:empty nil}])
        column-count (count fst)
        column-idxs (vec (keys fst))
        cursor (atom -1)
        total (dec (count all))]
    (reify
      ResultSet
      (getMetaData [_]
        (reify
          ResultSetMetaData
          (getColumnCount [_] column-count)
          (getColumnLabel [_ idx] (name (get column-idxs (dec idx))))))
      (getObject [_ ^int i]
        (let [k (get column-idxs (dec i))]
          (get (nth all @cursor) k)))
      (next [_]
        (if (< @cursor total)
          (do
            (swap! cursor inc)
            true)
          false))
      (close [_]))))

(declare visitor)

(defn accept [item]
  (let [p (promise)]
    (.accept item (visitor p))
    @p))

(defn columns [ps]
  (let [c (map accept (.getSelectItems ps))]
    (if (= c [:*])
      c
      (->> c
           (map (fn [x] ((:filter x) nil)))
           (map keyword)))))

(defn visitor [p]
  (reify

    StatementVisitor
    (^void visit [vstr ^Select stmt]
      (let [b (.getSelectBody stmt)]
        (.accept b (visitor p))))

    FromItemVisitor
    (^void visit [vstr ^Table tbl]
      (deliver p (.getName tbl)))

    SelectVisitor
    (^void visit [vstr ^PlainSelect ps]
      (deliver
       p
       (fn [api-key params]
         (let [[table] (map accept (.getFromItems ps))
               columns (columns ps)
               where (when-let [w (.getWhere ps)]
                       (accept w))
               where-url (if where
                           (try
                             ((:url where) (atom params))
                             (catch Exception _ ""))
                           "")
               where-filter (if where ((:filter where) (atom params)) "")
               [table-info] (project-map1 api-key (str "name:" table))
               table-id (:id table-info)
               filter-fun (if where-filter
                            (eval `(fn [~'record] ~where-filter))
                            (constantly true))
               select-fun (if (=  columns [:*])
                            identity
                            #(select-keys % columns))
               sort-keys (map keyword (map accept (.getOrderByElements ps)))
               sort-fun (if (seq sort-keys)
                          (partial sort (fn [a b]
                                          (loop [[k & ks] sort-keys]
                                            (let [i (compare (get a k)
                                                             (get b k))]
                                              (if (and (seq ks)
                                                       (zero? i))
                                                (recur ks)
                                                i)))))
                          identity)]
           (->> (project-stories api-key table-id where-url)
                sort-fun
                (filter filter-fun)
                (map select-fun))))))

    OrderByVisitor
    (^void visit [vstr ^OrderByElement obe]
      (p ((:filter (accept (.getColumnReference obe))) nil)))

    SelectItemVisitor
    (^void visit [vstr ^AllColumns sei]
      (p :*))
    (^void visit [vstr ^SelectExpressionItem sei]
      (.accept (.getExpression sei)
               (visitor p)))

    ExpressionVisitor
    (^void visit [vstr ^Column clm]
      (let [n (.getColumnName clm)]
        (deliver p {:url (fn [_]
                           (when (#{"phase"} n)
                             (throw (Exception.)))
                           n)
                    :filter (fn [_] n)})))
    (^void visit [vstr ^OrExpression eq]
      (let [le (accept (.getLeftExpression eq))
            re (accept (.getRightExpression eq))]
        (deliver p {:url #(format "(%s) OR (%s)"
                                  ((:url le) %)
                                  ((:url re) %))
                    :filter (fn [params]
                              `(or ~((:filter le) params)
                                   ~((:filter re) params)))})))
    (^void visit [vstr ^AndExpression eq]
      (let [le (accept (.getLeftExpression eq))
            re (accept (.getRightExpression eq))]
        (deliver p {:url #(format "(%s) AND (%s)"
                                  ((:url le) %)
                                  ((:url re) %))
                    :filter (fn [params]
                              `(and ~((:filter le) params)
                                    ~((:filter re) params)))})))
    (^void visit [vstr ^EqualsTo eq]
      (let [le (accept (.getLeftExpression eq))
            re (accept (.getRightExpression eq))]
        (deliver p {:url #(format "%s:%s"
                                  ((:url le) %)
                                  ((:url re) %))
                    :filter (fn [params]
                              `(= (~(keyword ((:filter le) params)) ~'record)
                                  ~((:filter re) params)))})))
    (^void visit [vstr ^StringValue sv]
      (deliver
       p
       {:url (fn [_] (pr-str (.getValue sv)))
        :filter (fn [_] (.getValue sv))}))
    (^void visit [vstr ^JdbcParameter param]
      (deliver
       p
       {:url (fn [params]
               (let [x (first @params)]
                 (swap! params rest)
                 (pr-str x)))
        :filter (fn [params]
                  (let [x (first @params)]
                    (swap! params rest)
                    x))}))))

(defn prepare-sql [sql]
  (accept
   (.parse (CCJSqlParserManager.)
           (java.io.StringReader. sql))))

(defn prepared-statement [api-key statement projects]
  (let [statement (.replace statement "?" "%s")
        params (atom {})]
    (reify
      PreparedStatement
      (executeQuery [_]
        (let [params (map pr-str (map second (sort-by first @params)))]
          (result-set ((prepare-sql statement) api-key params))))
      (setObject [_ idx value]
        (swap! params assoc idx value))
      (close [_]))))

(defn connection [api-key]
  (let [projects (project-map api-key)]
    (reify
      Connection
      (prepareStatement [_ statement]
        (prepared-statement api-key statement projects))
      (close [_]))))

(let [drvr (reify
             Driver
             (acceptsURL [_ url]
               (.contains url "agilezen:"))
             (connect [driver url properties]
               (when (.acceptsURL driver url)
                 (connection (.get properties "api-key"))))
             (getMajorVersion [_] 0)
             (getMinorVersion [_] 1)
             (getPropertyInfo [_ url info])
             (jdbcCompliant [_] false))]
  (DriverManager/registerDriver drvr)
  (def driver-class (.getName (class drvr))))
