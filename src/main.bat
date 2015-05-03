(clear)
(reset)
(load "../ontologia/ontologia.pont")
(load-instances "../ontologia/ontologia.pins")

(load "consultas.clp")

(make-instance alumno-x of Alumno (id 111)) ;test

;(run)
