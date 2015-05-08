;;
;; Estructuras para la asociacion heuristica de un problema abstracto a una solucion abstracta
;;

(deftemplate asignat "Asignatura recomendada con sus motivos"
    (slot asign (type INSTANCE))
    (multislot motivos (default (create$)))
    ;añadir también el grado de recomendación? [altamente recomendable, recomendable]
)

(deftemplate solucion-abstracta "Asignaturas a recomendar"
    (multislot list-asigns (default (create$)))
)

(defrule entrada-asociacion "Asociacion heuristica del problema"
    ?hecho <- (abstraccion ok)
    =>
    ;;; TODO: asociacion del problema ;;;
    (printout t "Asociacion del problema" crlf)

    (assert(ent-asigs))
    (retract ?hecho)
)

(defrule escoge-horario-preferidoR
    ?prob-abs <- (problema-abstracto (horario-preferidoR ?td))
    ?sol-abs <- (solucion-abstracta)
    =>
    (bind ?res (create$))
    (bind ?ins-asigs (find-all-instances ((?ins Asignatura))
        (member ?td (create$ (progn$ (?cand (send ?ins get-horarios)) (insert$ ?res (+ 1 (length$ ?res)) (send ?cand get-horario)))))
    ))

    ;;; TODO: añadir a solucion-abstracta ;;;
)

(defrule escoge-asigns
    ?hecho <- (ent-asigs)
    ?abs <- (problema-abstracto)
    =>

    ;;; TODO: mirar las asignaturas y escoger segun el problema abstracto ;;;

    (assert (solucion-abstracta))
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
