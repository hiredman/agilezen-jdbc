(ns agilezen-jdbc.core
  (require [clojure.contrib.sql :as sql]
           [clj-http.client :as http]
           [org.danlarkin.json :as json])
  (:import (java.sql Connection Driver DriverManager
                     PreparedStatement Statement ResultSet
                     ResultSetMetaData)
           (net.sf.jsqlparser.parser CCJSqlParserManager)
           (net.sf.jsqlparser.statement.select AllColumns Select)
           (net.sf.jsqlparser.expression.operators.relational EqualsTo
                                                              NotEqualsTo)
           (net.sf.jsqlparser.expression.operators.conditional AndExpression)
           (net.sf.jsqlparser.expression LongValue Function)
           (net.sf.jsqlparser.schema Column)
           (net.sf.jsqlparser.statement.update Update)))

(def project-list-url "https://agilezen.com/api/v1/projects")

(def story-list-url "https://agilezen.com/api/v1/projects/%s/stories")

(def story-url "https://agilezen.com/api/v1/projects/%s/stories/%s")

(defn project-map [api-key]
  (->> (http/get project-list-url
                 {:headers {"X-Zen-ApiKey" api-key}})
       :body
       json/decode
       :items
       (map (juxt (comp #(.toLowerCase %) :name) :id))
       (into {})))

(defn project-stories [api-key story-id & [filters]]
  (let [results (->> (http/get (format story-list-url story-id)
                               {:headers {"X-Zen-ApiKey" api-key}
                                :query-params {"pageSize" 1000
                                               "where" filters}})
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
                      (assoc :project (.toLowerCase (:name (:phase item))))))))
      {:count total})))

(defn result-set [[fst & rst :as all]]
  (let [column-count (count fst)
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

(defmulti where-clause (fn [o & args] (type o)))

(defmethod where-clause AndExpression [and-expr url?]
  (if-not url?
    `(and ~(where-clause (.getLeftExpression and-expr) url?)
          ~(where-clause (.getRightExpression and-expr) url?))
    (format "(%s) AND (%s)"
            (where-clause (.getLeftExpression and-expr) url?)
            (where-clause (.getRightExpression and-expr) url?))))

(defmethod where-clause EqualsTo [equals url?]
  (if-not url?
    (let [field (keyword (where-clause (.getLeftExpression equals) url?))
          value (where-clause (.getRightExpression equals) url?)]
      `(= (~field ~'record) ~value))
    (format "%s:%s"
            (where-clause (.getLeftExpression equals) url?)
            (where-clause (.getRightExpression equals) url?))))

(defmethod where-clause NotEqualsTo [nequals url?]
  (if-not url?
    (let [field (keyword (where-clause (.getLeftExpression nequals) url?))
          value (where-clause (.getRightExpression nequals) url?)]
      `(not= (~field ~'record) ~value))
    (format "not(%s:%s)"
            (where-clause (.getLeftExpression nequals) url?)
            (where-clause (.getRightExpression nequals) url?))))

(defmethod where-clause Column [col url?]
  (read-string (.getColumnName col)))

(defmethod where-clause LongValue [lv url?]
  (.intValue (.getValue lv)))

(defmulti execute-sql* (fn [o & _] (type o)))

(defn gimme-fields [expressions]
  (mapcat #(if (instance? AllColumns %)
             [:*]
             (let [expr (.getExpression %)]
               (if (instance? Function expr)
                 (cons [(.toString expr) @(resolve (symbol (.toLowerCase (.getName expr))))]
                       (map (fn [x] (keyword (where-clause x false)))
                            (seq (.getExpressions (.getParameters expr)))))
                 [(keyword
                   (.getColumnName
                    (.getExpression %)))])))
          expressions))

(defmethod execute-sql* Select [select api-key projects]
  (let [body (.getSelectBody select)
        table (.getName (first (.getFromItems body)))
        table-id (get projects table)
        fields (gimme-fields (.getSelectItems body))
        where (.getWhere body)
        url (when where (where-clause where true))
        filter-fun (if where
                     (eval `(fn [~'record]
                              ~(where-clause where false)))
                     (constantly true))
        map-funs (filter vector? fields)
        map-fun (if (seq map-funs)
                  (apply juxt
                         (map (fn [[name fun]]
                                (fn [x]
                                  {name (fun x)})) map-funs))
                  identity)
        fields (remove vector? fields)
        select-fun (if (= [:*] fields)
                     identity
                     #(select-keys % fields))]
    (result-set
     (map-fun
      (map select-fun
           (filter filter-fun (project-stories api-key table-id url)))))))

(defmethod execute-sql* Update [update api-key projects]
  (let [keys (map keyword (map where-clause (.getColumns update)))
        values (map where-clause (.getExpressions update))
        new-values (zipmap keys values)
        table (.getName (.getTable update))
        table-id (get projects table)
        where (.getWhere update)
        effected-stories (map :id (resultset-seq (execute-sql (format "SELECT id FROM %s WHERE %s" table (.toString where))
                                                              api-key
                                                              projects)))]
    (doseq [id effected-stories]
      (http/put (doto (format story-url table-id id) prn)
                {:headers {"X-Zen-ApiKey" api-key}
                 :body (doto (json/encode new-values)
                         println)}))
    (result-set [{:rows (count effected-stories)}])))

(defn execute-sql [statement api-key projects]
  (execute-sql*
   (.parse (CCJSqlParserManager.)
           (java.io.StringReader. statement))
   api-key
   projects))

(defn prepared-statement [api-key statement projects]
  (let [statement (.replace statement "?" "%s")
        params (atom {})]
    (reify
      PreparedStatement
      (executeQuery [_]
        (let [params (map pr-str (map second (sort-by first @params)))
              stmt (apply format statement params)]
          (execute-sql stmt api-key projects)))
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
