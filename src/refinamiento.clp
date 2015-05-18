;;
;; Estructuras para el refinamiento de una solucion abstracta a la solucion de nuestro problema
;;

(deffunction ha-cursado "Retorna si el alumno ?al ha cursado la asignatura ?a"
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

(deffunction creditos-aprobados "Obtiene los créditos aprobados del alumno ?al"
    (?al)

    (bind ?cred-apr 0)
    (bind ?notas (send (send ?al get-expediente_alumno) get-notas_exp))
    (progn$ (?ins ?notas)
        (if (>= (send ?ins get-nota) 5) then
            (bind ?cred-apr (+ ?cred-apr (send (send (send ?ins get-convocatoria_nota) get-asignatura_conv) get-num_creditos)))
        )
    )
    ?cred-apr
)


(defrule entrada-refinamiento "Asociacion heuristica del problema"
    ?hecho <- (asociacion ok)
    =>
    ;;; TODO: refinamiento del problema ;;;
    (printout t "Refinamiento del problema" crlf)

    (assert (filtro-restr))
    (assert (refina-rec))
    (retract ?hecho)
)

(defrule descarta-segun-rest "Descarta las candidatas que no cumplen todas las restricciones"
    (declare (salience 10))
    (nrestricciones ?nrest)
    (filtro-restr)
    ?ar <- (asig-rec (asign ?a) (rest-sat ?rs) (motivosP $?mP))
    ;(test (!= ?nrest ?rs))
    =>
    (if (!= ?nrest ?rs)
        then
        (if (member asignatura-suspensa ?mP)
            then
            (printout t (send ?a get-nombre) " no cumple todas las restricciones, pero esta suspensa" crlf)
            else
            (printout t (send ?a get-nombre) " no cumple todas las restricciones (" ?rs "<" ?nrest ")"  crlf)
        (retract ?ar)
        )
    )
)

(defrule descarta-ya-aprobadas "Descarta las candidatas que ya se hayan cursado y aprobado"
    (declare (salience 9))
    (refina-rec)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    ?ar <- (asig-rec (asign ?a))
    (test (ha-aprobado ?al ?a))
    =>
    (printout t (send ?a get-nombre) " ya esta aprobada" crlf)
    (retract ?ar)
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

(defrule descarta-optativas "Descarta las asignaturas optativas si no se ha superado la fase inicial (60 créditos ECTS)"
    (declare (salience 7))
    (refina-rec)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    ?ar <- (asig-rec (asign ?a))
    (test (< (creditos-aprobados ?al) 60))
    (test (eq Optativa (class ?a)))
    =>
    (printout t (send ?a get-nombre) " es optativa y no se puede cursar" crlf)
    (retract ?ar)
)

(defrule refina
    ?hecho1 <- (refina-rec)
    ?hecho2 <- (filtro-restr)
    ?hecho3 <- (nrestricciones ?nrestr)
    
    =>

    (assert (refinamiento ok))
    (retract ?hecho1 ?hecho2 ?hecho3)
)

(defrule fin-refinamiento "Comprueba que se ejecuten todas las reglas de Refinamiento"
    ?hecho1 <- (refinamiento ok)
    =>
    ;;; esta regla elimina los hechos usados en el refinamiento y genera un assert conforme ha acabado ;;;
    (printout t "Fin refinamiento" crlf)
    (printout t crlf)
    (printout t "-------------" crlf)
    (printout t crlf)

    ;;; TODO: Mostrar la recomendacion ;;;
    (assert (muestra-sol))
    (retract ?hecho1)
)

(deffunction grado-recomendacion
    (?ps $?mP)
    
    (if (member asignatura-suspensa ?mP) then(return altamente-recomendable))
    
    (if (< ?ps 5)
        then (return recomendable)
        else
        else (return altamente-recomendable)
    )
)

(deffunction muestra-mot
    (?rs $?motivos)
    
    (loop-for-count (?i 1 (length$ ?motivos)) do
        (bind ?mot (nth$ ?i ?motivos))
        (printout t "  * " ?mot crlf)
    )
)

(defrule muestra-solucion
    (declare (salience 5))
    (muestra-sol)
    ?ar <- (asig-rec (asign ?a) (motivosR $?msR) (motivosP $?msP) (rest-sat ?rs) (pref-sat ?ps))
    =>
    (bind ?nomA (send ?a get-nombre))
    (bind ?gradoRec (grado-recomendacion ?ps ?msP))
    (format t "%s (%s): %n" ?nomA ?gradoRec)
    (printout t " * Restricciones" crlf)
    (muestra-mot ?rs ?msR)
    (printout t " * Preferencias" crlf)
    (muestra-mot ?ps ?msP)
    
    ;; TODO: guardar la asignatura y sus motivos en la clase
    ;; añadirlas en la lista de forma ordenada segun el grado de recomendacion
    
    (retract ?ar)
)

(defrule descarta-num
    ?hecho <- (muestra-sol)
    =>
    
    ;;; TODO: en esta regla deberiamos tener ya una lista de las posibles asignaturas a recomendar
    ;;; como la lista esta ordenada segun el grado de recomendacion, seria en un bucle mirar:
    ;;; 1. escoger un grupo de maxAsigs
    ;;; 2. mirar que cumpla tiempo-dedicacion
    ;;; 3. mirar que cumple corequisitos (dentro de las asigs escogidas en 1)
    ;;; si se cumple, tenemos solucion. Sino, quitar la ultima del grupo (la de menos grado), escoger la siguiente y otra vez al bucle.
    
    (retract ?hecho)
)

