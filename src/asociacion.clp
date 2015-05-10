;;
;; Estructuras para la asociacion heuristica de un problema abstracto a una solucion abstracta
;;

(deftemplate asig-rec "Asignatura recomendada con sus motivos (a partir de todas las reglas)"
    (slot asign)
    (multislot motivos (default (create$)))
    (slot pref-sat) ;número de preferencias que satisface
    ;añadir también el grado de recomendación? [altamente recomendable, recomendable]
)

(deftemplate solucion-abstracta "Asignaturas recomendadas" ; ya no es necesario (?)
    (multislot list-asigns (default (create$)))
)

(deftemplate nueva-rec "Nueva asignatura recomendada por una regla"
    (slot asign)
    (slot motivo)
    (slot es-pref)
)

(defrule modifica-asig-rec "Modifica una asignatura recomendada (añade motivo y/o pref-sat)"
    (declare (salience 10)) ;tiene prioridad para comprobar si ya existe la asig-rec
    ?nr <- (nueva-rec (asign ?a) (motivo ?m) (es-pref ?ep))
    ?ar <- (asig-rec (asign ?a) (motivos $?ms) (pref-sat ?ps))
    =>
    (if (eq ep TRUE)
        then (bind ?ps-nuevo (+ 1 ?ps))
        else (bind ?ps-nuevo ?ps)
    )
    (bind ?ar (modify ?ar (motivos (insert$ ?ms 1 ?m)) (pref-sat ?ps-nuevo)))

    (retract ?nr)
)

(defrule anade-asig-rec "Añade una nueva asignatura recomendada (antes no existía)"
    ?nr <- (nueva-rec (asign ?a) (motivo ?m) (es-pref ?ep))
    (not (exists (asig-rec (asign ?a))))
    =>
    (if (eq ep TRUE)
        then (bind ?ps 1)
        else (bind ?ps 0)
    )
    (assert (asig-rec (asign ?a) (motivos (create$ ?m)) (pref-sat ?ps)))

    (retract ?nr)
)


(defrule entrada-asociacion "Asociacion heuristica del problema"
    ?hecho <- (abstraccion ok)
    =>
    ;;; TODO: asociacion del problema ;;;
    (printout t "Asociacion del problema" crlf)

    (assert (solucion-abstracta (list-asigns (create$))))
    (assert(ent-asigs))
    (retract ?hecho)
)

(defrule escoge-horario-preferidoR
    (asigs ok)
    ?prob-abs <- (problema-abstracto (horario-preferidoR ?td))
    =>
    (bind ?res (create$))
    (bind ?ins-asigs (find-all-instances ((?ins Asignatura))
        (member ?td (create$ (progn$ (?cand (send ?ins get-horarios)) (insert$ ?res (+ 1 (length$ ?res)) (send ?cand get-horario)))))
    ))

    (loop-for-count (?i 1 (length$ ?ins-asigs)) do
        (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo "horario-preferido") (es-pref FALSE)))
    )
)



(defrule escoge-asigns
    ?hecho <- (ent-asigs)
    ?abs <- (problema-abstracto)
    =>

    ;;; TODO: mirar las asignaturas y escoger segun el problema abstracto ;;;

    (assert (asigs ok))
    (retract ?hecho)
)

(defrule fin-asociacion "Comprueba que se ejecuten todas las reglas de Asociacion"
    ?hecho1 <- (asigs ok)
    =>
    ;;; esta regla elimina los hechos usados en la asociacion y genera un assert conforme ha acabado ;;;
    (printout t "Fin asociacion" crlf)
    (assert(asociacion ok))
    (retract ?hecho1)
)
