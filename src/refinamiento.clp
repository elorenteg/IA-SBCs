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

(defrule descarta-segun-requisitos "Descarta las candidatas que incumplan los requisitos entre asignaturas"
    (declare (salience 8))
    (refina-rec)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    ?ar <- (asig-rec (asign ?a))
    =>
    (bind ?prerrequisitos (send ?a get-prerrequisitos))
    (bind ?correquisitos (send ?a get-correquisitos))
    (bind ?precorrequisitos (send ?a get-precorrequisitos))
    (bind ?orrequisitos (send ?a get-orrequisitos))

    (loop-for-count (?i 1 (length$ ?prerrequisitos)) do
        (if (not (ha-aprobado ?al (nth$ ?i ?prerrequisitos)))
            then
            (printout t (send ?a get-nombre) " no cumple prerrequisitos" crlf)
            (retract ?ar)
            (break)
        )
    )

    (loop-for-count (?i 1 (length$ ?correquisitos)) do
        (if (not (or (ha-aprobado ?al (nth$ ?i ?correquisitos)) TRUE)) ;cómo compruebo si "está matriculado" de una asignatura? Si está entre las candidatas?
            then
            (printout t (send ?a get-nombre) " no cumple correquisitos" crlf)
            (retract ?ar)
            (break)
        )
    )

    (loop-for-count (?i 1 (length$ ?precorrequisitos)) do
        (if (not (ha-cursado ?al (nth$ ?i ?precorrequisitos)))
            then
            (printout t (send ?a get-nombre) " no cumple precorrequisitos" crlf)
            (retract ?ar)
            (break)
        )
    )

    (bind ?orreq-alguna FALSE)
    (loop-for-count (?i 1 (length$ ?orrequisitos)) do
        (if (ha-aprobado ?al (nth$ ?i ?orrequisitos))
            then
            (bind ?orreq-alguna TRUE)
            (break)
        )
    )
    (if (and (> (length$ ?orrequisitos) 0) (eq ?orreq-alguna FALSE))
        then
        (printout t (send ?a get-nombre) " no cumple orrequisitos" crlf)
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