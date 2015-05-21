;;
;; Estructuras para el refinamiento de una solucion abstracta a una solucion concreta
;;

(defmodule refinamiento "Módulo para el refinamiento de una solucion abstracta a una solucion concreta"
    (import MAIN ?ALL)
    (import consultas deftemplate dni)
    (import respref deftemplate respref)
    (import respref deftemplate nrestricciones)
    (import asociacion deftemplate asig-rec)
    (import asociacion deffunction ha-aprobado)
    (export ?ALL)
)


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
    (declare (salience 10))
    =>
    ;;; TODO: refinamiento del problema ;;;
    (printout t "Refinamiento del problema" crlf)

    (assert (filtro-restr))
    (assert (refina-rec))
    (assert (candidatas (create$)))
)

(defrule descarta-segun-rest "Descarta las candidatas que no cumplen todas las restricciones"
    (nrestricciones ?nrest ?nrestf)
    (filtro-restr)
    ?ar <- (asig-rec (asign ?a) (rest-sat ?rs) (motivosP $?mP))
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
    (refina-rec)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    ?ar <- (asig-rec (asign ?a))
    (test (ha-aprobado ?al ?a))
    =>
    ;(printout t (send ?a get-nombre) " ya esta aprobada" crlf)
    (retract ?ar)
)

(defrule descarta-segun-requisitos "Descarta las candidatas que incumplan los requisitos entre asignaturas"
    (refina-rec)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    ?ar <- (asig-rec (asign ?a))
    =>
    (bind ?prerrequisitos (send ?a get-prerrequisitos))
    (bind ?precorrequisitos (send ?a get-precorrequisitos))
    (bind ?orrequisitos (send ?a get-orrequisitos))

    (loop-for-count (?i 1 (length$ ?prerrequisitos)) do
        (if (not (ha-aprobado ?al (nth$ ?i ?prerrequisitos)))
            then
            ;(printout t (send ?a get-nombre) " no cumple prerrequisitos" crlf)
            (retract ?ar)
            (break)
        )
    )

    (loop-for-count (?i 1 (length$ ?precorrequisitos)) do
        (if (not (ha-cursado ?al (nth$ ?i ?precorrequisitos)))
            then
            ;(printout t (send ?a get-nombre) " no cumple precorrequisitos" crlf)
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
        ;(printout t (send ?a get-nombre) " no cumple orrequisitos" crlf)
        (retract ?ar)
    )
)

(defrule descarta-optativas "Descarta las asignaturas optativas si no se ha superado la fase inicial (60 créditos ECTS)"
    (refina-rec)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    ?ar <- (asig-rec (asign ?a))
    (test (< (creditos-aprobados ?al) 60))
    (test (eq Optativa (class ?a)))
    =>
    ;(printout t (send ?a get-nombre) " es optativa y no se puede cursar" crlf)
    (retract ?ar)
)

(defrule refina
    ?hecho1 <- (refina-rec)
    ?hecho2 <- (filtro-restr)

    =>

    (assert (refinamiento ok))
    (retract ?hecho1 ?hecho2)
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
    (declare (salience 1))
    ?hecho <- (agrupa)
    ?ar <- (asig-rec (asign ?a) (motivosR $?msR) (motivosP $?msP) (rest-sat ?rs) (pref-sat ?ps))
    ?cand <- (candidatas $?list)
    =>
    (bind ?ins (make-instance of asig-candidata (asig ?a) (motivosR ?msR) (motivosP ?msP) (grado (grado-recomendacion ?ps ?msP))))
    (bind $?list (subseq$ (inserta-ordenado ?ins $?list) 1 12)) ;nos quedamos con las 12 mejores candidatas

    (retract ?cand)
    (assert (candidatas ?list))

    (assert (filtra-nasig))
    (retract ?ar)
)



(defrule backtracking
    ?hecho1 <- (no-solution)
    ?hecho2 <- (backtrack ?i $?grupo)
    ?cand <- (candidatas $?list)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    ?rest <- (respref (es_restriccion TRUE) (max_asigns ?ma) (max_horas_trabajo ?mht) (max_horas_lab ?mhl))

    =>

    (if (eq ?i (+(length$ ?list)1))
        then
        (bind ?correq-ok TRUE)
        (loop-for-count (?j 1 (length$ ?grupo)) do
            (bind ?correquisitos (send (send (nth$ ?j ?grupo) get-asig) get-correquisitos))
            (loop-for-count (?k 1 (length$ ?correquisitos)) do
                (if (not (or (ha-aprobado ?al (nth$ ?k ?correquisitos)) (member (nth$ ?k ?correquisitos) ?grupo))) then
                    (bind ?correq-ok FALSE)
                    (break)
                )
            )
        )

        (bind ?sum-horas 0)
        (loop-for-count (?j 1 (length$ ?grupo)) do
            ;divido las horas totales entre 18 semanas lectivas, porque la res/pref está en horas semanales
            (bind ?sum-horas (+ ?sum-horas (/ (send (send (nth$ ?j ?grupo) get-asig) get-horas_teoria) 18) (/ (send (send (nth$ ?j ?grupo) get-asig) get-horas_prob) 18)))
        )

        (bind ?sum-horas-lab 0)
        (loop-for-count (?j 1 (length$ ?grupo)) do
            (bind ?sum-horas-lab (+ ?sum-horas-lab (/ (send (send (nth$ ?j ?grupo) get-asig) get-horas_lab) 18)))
        )


        (if (and (eq ?correq-ok TRUE)
                 (or (eq ?mht nil) (<= ?sum-horas ?mht))
                 (or (eq ?mhl nil) (<= ?sum-horas-lab ?mhl))
                 (or (and (eq ?ma nil) (= (length$ ?grupo) 6))
                     (and (neq ?ma nil) (= (length$ ?grupo) ?ma))))
            then
            ;;; TODO: revisar si se cumplen las preferencias de horas y número de asignaturas?
            (printout t "SOLUCION " ?grupo crlf)
            (retract ?hecho1)
            (assert (solucion ?grupo))
            (focus presentacion)
        )

        else
        (assert (backtrack (+ ?i 1) ?grupo))
        (bind ?asig (nth$ ?i ?list))
        (bind $?grupoCon (insert$ ?grupo (+(length$ ?grupo)1) ?asig))
        (assert (backtrack (+ ?i 1) ?grupoCon))
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
    (printout t "COMPLETO " ?list crlf)

    (assert (no-solution))
    (assert (backtrack 1 (create$)))
    (retract ?hecho)
)







(defmodule presentacion "Módulo para la presentacion de resultados"
    (import MAIN ?ALL)
    (import respref deftemplate respref)
    (import respref deftemplate nrestricciones)
    (import refinamiento deftemplate solucion)
    (export ?ALL)
)

(deffunction separa
    (?mot)
    
    (bind ?p1 (str-index "-" ?mot))
    (bind ?mot1 (sub-string (+ ?p1 1) (str-length ?mot) ?mot))
    (return ?mot1)
)

(deffunction lista-motivo
    (?titulo ?idMot $?motivos)
    
    (bind ?first FALSE)
    (bind ?string "")
    (loop-for-count (?i 1 (length$ ?motivos)) do
        (bind ?mot (nth$ ?i ?motivos))
        (if (not(eq (str-index ?idMot ?mot) FALSE))
            then
            (if (eq ?first TRUE) then
                (bind ?string (str-cat ?string ", "))
            )
            (bind ?string (str-cat ?string (separa ?mot)))
            (bind ?first TRUE)
        )
    )
    
    (if (not (eq (str-compare "" ?string) 0))
        then
        (printout t " * " ?titulo ": " ?string crlf)
    )
)

(deffunction muestra-motivos
    ($?motivos)
    
    (if (member asignatura-suspensa ?motivos) then
        (printout t " * Asignatura suspendida" crlf)
    )
    (lista-motivo "Sigue plan de estudios" "sigue plan estudios" ?motivos)
    (lista-motivo "Dificultad" "dificultad" ?motivos)
    (lista-motivo "Tipo de Horario" "horario preferido" ?motivos)
    (lista-motivo "Especialidad" "completar especialidad" ?motivos)
    (lista-motivo "Temas" "intereses tematicos" ?motivos)
    (lista-motivo "Competencias" "intereses competencias" ?motivos)
    
    ;(printout t "nprefs: " (length$ ?motivos) crlf)
)

(defrule muestra-solucion
    (declare (salience 10))
    ?sol <- (solucion $?list)
    ;(nrestricciones ?nrest ?nrest-final)
    ?rest <- (respref (es_restriccion TRUE) (competencias_preferidas $?cp) (completar_especialidad ?ce) (max_asigns ?ma) 
                 (max_horas_trabajo ?mht) (max_horas_lab ?mhl) (tema_especializado $?te) (tipo_horario $?th))
    =>
    
    (printout t "=====================================================================" crlf)
    (printout t "=                           Recomendacion                           =" crlf)
    (printout t "=====================================================================" crlf)
    (printout t crlf)
    
    (bind ?nrest 0)
    (bind ?nrest-final 0)
    (if (> (+ ?nrest ?nrest-final) 0) 
        then
        (printout t "Restricciones aplicadas a la solucion:" crlf)
        (if (neq ?ma nil) then (printout t " - Num. asignaturas a matricular: " ?ma crlf))
        (if (neq ?mht nil) then (printout t " - Max. horas de dedicacion semanales: " ?mht crlf))
        (if (neq ?mhl nil) then (printout t " - Max. horas de laboratorio/problemas semanales: " ?mhl crlf))
        (if (eq (length$ ?th) 1) then (printout t " - Tipo de horario: " (send (nth$ 1 ?th) get-horario) crlf))
        (if (> (length$ ?te) 0) 
            then 
            (printout t " - Temas de interes: ")
            (loop-for-count (?i 1 (length$ ?te)) do
                (printout t (send (nth$ ?i ?te) get-nombre_tema))
                (if (< ?i (length$ ?te)) then (printout t ", "))
            )
            (printout t crlf)
        )
        (if (neq ?ce nil) then (printout t " - Especialidad: " (send ?ce get-nombre_esp) crlf))
        (if (> (length$ ?cp) 0) 
            then 
            (printout t " - Competencias transversales: ")
            (loop-for-count (?i 1 (length$ ?cp)) do
                (printout t (send (nth$ ?i ?cp) get-nombre_comp))
                (if (< ?i (length$ ?cp)) then (printout t ", "))
            )
            (printout t crlf)

        ) 
        (printout t crlf crlf)
    )

    (printout t "Asignaturas recomendadas:" crlf)
    (printout t crlf)
    
    (loop-for-count (?i 1 (length$ ?list)) do
        (bind ?asig (nth$ ?i ?list))
        (bind ?asigI (send ?asig get-asig))
        (bind ?nomA (send ?asigI get-nombre))
        (bind $?motP (send ?asig get-motivosP))
        (bind ?gradoRec (send ?asig get-grado))
        (format t "%s (%s): %n" ?nomA ?gradoRec)
        (muestra-motivos ?motP)
        (printout t crlf)
    )
)