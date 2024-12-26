(ns user
  (:require [cloroutine.core :refer [cr]]))

(macroexpand-1 '(cr {} (js* "'~{}'" "yo")))
