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
    (declare (salience 10))
    (nrestricciones ?nrest)
    (filtro-restr)
    ?ar <- (asig-rec (asign ?a) (rest-sat ?rs))
    =>
    (if (!= ?nrest ?rs) then (retract ?ar))
    (assert (refina-rec))
)

(defrule descarta-ya-cursadas "Descarta las candidatas que ya se hayan cursado"
    (declare (salience 8))
    (refina-rec)
    ?ar <- (asig-rec (asign ?a))
    ?al <- (object (is-a Alumno) (id ?dni))
    =>
    (bind ?nombre-cand (send ?a get-nombre))
    (bind ?notas (send (send ?al get-expediente_alumno) get-notas_exp))
    (progn$ (?ins ?notas)
        (if (eq ?nombre-cand (send (send (send ?ins get-convocatoria_nota) get-asignatura_conv) get-nombre))
            then
            (retract ?ar)
            (break)
        )
    )
)

(defrule refina
    ?hecho <- (refina-rec)

    =>

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