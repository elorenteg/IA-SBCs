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

    (assert (filtro-restr))
    (retract ?hecho)
)

(defrule descarta-segun-rest "Descarta las candidatas que no cumplen todas las restricciones"
    (declare (salience 10)) ;alguna forma más elegante para que "refina" sólo se ejecute cuando no se pueda aplicar más esta regla?
    (nrestricciones ?nrest)
    (filtro-restr)
    ?ar <- (asig-rec (asign ?a) (rest-sat ?rs))
    =>
    (if (!= ?nrest ?rs) then (retract ?ar))
    (assert (refina-rec))
)

(defrule refina
    ?hecho <- (refina-rec)

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
    (assert (muestra-sol))
    (retract ?hecho1)
)

(defrule muestra-solucion
    (muestra-sol)
    ?ar <- (asig-rec (asign ?a) (motivos $?ms))
    =>
    (printout t (send ?a get-nombre) ": " ?ms crlf)
)