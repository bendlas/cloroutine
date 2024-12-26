(ns user
  (:require [cloroutine.core :refer-macros [cr]]))

(macroexpand-1 '(cr {} (js* "'~{}'" "yo")))
