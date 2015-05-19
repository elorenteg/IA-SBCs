;;
;; Estructuras para el refinamiento de una solucion abstracta a la solucion de nuestro problema
;;

(defclass asig-candidata
    (is-a USER)
    (slot asig)
    (multislot motivosR)
    (multislot motivosP)
    (slot grado)
)

(deftemplate recomendacion
    (multislot asigs-recom)
)

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
    (assert (candidatas (create$)))
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
    (printout t "Fin refinamiento" crlf)
    (printout t crlf)
    (printout t "-------------" crlf)
    (printout t crlf)

    (assert (agrupa))
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

(deffunction inserta-ordenado
    (?ins $?list)
    (bind $?motivosP (send ?ins get-motivosP))
    
    (bind ?preferente FALSE)
    (if (member asignatura-suspensa ?motivosP) then (bind ?preferente TRUE))
 
    (bind ?insertat FALSE)
    (loop-for-count (?i 1 (length$ ?list)) do
        (bind ?asig (nth$ ?i ?list))
        (bind $?motP (send ?asig get-motivosP))
        (if (eq ?preferente TRUE)
            then
            (bind $?list (insert$ ?list ?i ?ins))
            (bind ?insertat TRUE)
            (break)
        )
        (if (> (length$ ?motivosP) (length$ ?motP))
            then ; ?ins es mas recomendable que ?asig
            (bind $?list (insert$ ?list ?i ?ins))
            (bind ?insertat TRUE)
            (break)
        )
    )
    
    (if (not ?insertat) then (bind $?list (insert$ ?list (+(length$ ?list)1) ?ins)))
    (return $?list)
)

(defrule obtiene-candidatas "Agrupa las asignaturas que se pueden recomendar"
    (declare (salience 6))
    ?hecho <- (agrupa)
    ?ar <- (asig-rec (asign ?a) (motivosR $?msR) (motivosP $?msP) (rest-sat ?rs) (pref-sat ?ps))
    ?cand <- (candidatas $?list)
    =>
    (bind ?ins (make-instance of asig-candidata (asig ?a) (motivosR ?msR) (motivosP ?msP) (grado (grado-recomendacion ?ps ?msP))))
    (bind $?list (inserta-ordenado ?ins $?list))
    
    (retract ?cand)
    (assert (candidatas ?list))
    
    (assert (filtra-nasig))
    (retract ?ar)
)



(defrule backtracking
    ?hecho1 <- (no-solution)
    ?hecho2 <- (backtrack ?i $?grupo)
    ?cand <- (candidatas $?list)
    
    =>
    
    (if (eq ?i (+(length$ ?list)1))
        then
        (printout t "SOLUCION " ?grupo crlf)
        ; mirar si cumple:
        ; 1. numAsigs
        ; 2. numHoras
        ; 3. corequisitos (matriculacion)
        ; si cumple -> (muestra-sol ?grupo) y 
        (if (eq (length$ ?grupo) 6) ;;; Esto solo es una prueba
            then
            (retract ?hecho1)
            (assert (solucion ?grupo))
        )
        
        else
        (bind ?asig (nth$ ?i ?list))
        (bind $?grupoCon (insert$ ?grupo (+(length$ ?grupo)1) ?asig))
        (assert (backtrack (+ ?i 1) ?grupoCon))
        (assert (backtrack (+ ?i 1) ?grupo))
    )
    
    (retract ?hecho2)
)

(defrule filtra-final
    ?hecho <- (filtra-nasig)
    ?hecho2 <- (agrupa)
    ?rest <- (respref (es_restriccion TRUE) (max_asigns ?maR))
    ?pref <- (respref (es_restriccion FALSE) (max_asigns ?maP))
    ?cand <- (candidatas $?list) ;;; $?list esta ordenado segun el numero de preferencias
    =>
    ;(bind ?list (find-all-instances ((?a asig-candidata)) (eq altamente-recomendable ?a:grado)))
    ;(bind ?list (insert$ ?list (+ 1 (length$ ?list)) (find-all-instances ((?a asig-candidata)) (eq recomendable ?a:grado))))
    ;?list contiene todas las asignaturas candidatas, primero las altamente-recomendable, luego las recomendable
    
    (printout t "COMPLETO " ?list crlf)
    (assert (solucion ?list))

    (assert (no-solution))
    (assert (backtrack 1 (create$)))
    (retract ?hecho)
)



(deffunction muestra-motivos
    ($?motivos)

    (loop-for-count (?i 1 (length$ ?motivos)) do
        (bind ?mot (nth$ ?i ?motivos))
        (printout t "  * " ?mot crlf)
    )
)

(defrule muestra-solucion
    (declare (salience 5))
    ?sol <- (solucion $?list)
    =>
    (loop-for-count (?i 1 (length$ ?list)) do
        (bind ?asig (nth$ ?i ?list))
        (bind ?asigI (send ?asig get-asig))
        (bind ?nomA (send ?asigI get-nombre))
        (bind $?motR (send ?asig get-motivosR))
        (bind $?motP (send ?asig get-motivosP))
        (bind ?gradoRec (send ?asig get-grado))
        (format t "%s (%s): %n" ?nomA ?gradoRec)
        (printout t " * Restricciones" crlf)
        (muestra-motivos ?motR)
        (printout t " * Preferencias" crlf)
        (muestra-motivos ?motP)
    )
)