;;
;; Estructuras para el refinamiento de una solucion abstracta a la solucion de nuestro problema
;;

(deftemplate solucion-concreta "Asignaturas que se recomiendan"
    (multislot list-asigns (default (create$)))
)

(defrule entrada-refinamiento "Asociacion heuristica del problema"
    ?hecho <- (asociacion ok)
    =>
    ;;; TODO: refinamiento del problema ;;;
    (printout t "Refinamiento del problema" crlf)

    (assert (refina-rec))
    (retract ?hecho)
)

(defrule refina
    ?hecho <- (refina-rec)
    ?nrest <- (nrestricciones ?nrest)

    =>

    ;;;; TODO: eliminar "asig-rec"s que no tengan el slot rest-sat == ?nrest ;;;

    (assert (refinamiento ok))
    (retract ?hecho)
)

(defrule fin-refinamiento "Comprueba que se ejecuten todas las reglas de Refinamiento"
    ?hecho1 <- (refinamiento ok)
    =>
    ;;; esta regla elimina los hechos usados en el refinamiento y genera un assert conforme ha acabado ;;;
    (printout t "Fin refinamiento" crlf)

    ;;; TODO: Mostrar la recomendacion ;;;

    (retract ?hecho1)
)