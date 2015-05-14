;;
;; Estructuras para el refinamiento de una solucion abstracta a la solucion de nuestro problema
;;

(deftemplate solucion-concreta "Asignaturas que se recomiendan"
    (multislot list-asigns (default (create$)))
)


(deffunction ha-aprobado
    (?al ?a)

    (bind ?nombre-cand (send ?a get-nombre))
    (bind ?notas (send (send ?al get-expediente_alumno) get-notas_exp))
    (progn$ (?ins ?notas)
        (if (and (eq ?nombre-cand (send (send (send ?ins get-convocatoria_nota) get-asignatura_conv) get-nombre)) (>= (send ?ins get-nota) 5))
            then
            (return TRUE)
        )
    )
    (return FALSE)
)

(deffunction ha-cursado
    (?al ?a)

    (bind ?nombre-cand (send ?a get-nombre))
    (bind ?notas (send (send ?al get-expediente_alumno) get-notas_exp))
    (progn$ (?ins ?notas)
        (if (eq ?nombre-cand (send (send (send ?ins get-convocatoria_nota) get-asignatura_conv) get-nombre))
            then
            (return TRUE)
        )
    )
    (return FALSE)
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

(defrule descarta-ya-aprobadas "Descarta las candidatas que ya se hayan cursado y aprobado"
    (declare (salience 9))
    (refina-rec)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    ?ar <- (asig-rec (asign ?a))
    =>
    (if (ha-aprobado ?al ?a)
        then
        (printout t (send ?a get-nombre) " ya esta aprobada" crlf)
        (retract ?ar)
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