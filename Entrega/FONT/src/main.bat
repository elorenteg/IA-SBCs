(clear)
(reset)

(defmodule MAIN (export ?ALL))

(load "../ontologia/ontologia.pont")
(load-instances "../ontologia/ontologia.pins")

(load "consultas.clp")
(load "respref.clp")
(load "abstraccion.clp")
(load "asociacion.clp")
(load "refinamiento.clp")

;(run)

