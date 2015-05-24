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


(defclass asig-candidata "Asignatura candidata a aparecer en la solución final (ha pasado todos los filtros)"
    (is-a USER)
    (slot asig)
    (multislot motivosR)
    (multislot motivosP)
    (slot prioridad)
    (slot grado)
)

(deftemplate prefs-grupo "Contiene información sobre si se cumplen las preferencias de grupo"
    (slot cumple-max_asigns)
    (slot cumple-max_horas_trabajo)
    (slot cumple-max_horas_lab)
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
    (assert (filtro-restr))
    (assert (refina-rec))
    (assert (candidatas (create$)))
)

(defrule descarta-segun-rest "Descarta las candidatas que no cumplen todas las restricciones"
    (declare (salience 5))
    (nrestricciones ?nrest ?nrestf)
    (filtro-restr)
    ?ar <- (asig-rec (asign ?a) (rest-sat ?rs) (motivosR $?mR) (motivosP $?mP) (prioridad ?p))
    =>
    (if (< ?rs ?nrest) 
        then
        (if (member asignatura-suspensa ?mP)
            then
            ;(printout t (send ?a get-nombre) " no cumple todas las restricciones, pero esta suspensa" crlf)
            else
            ;(printout t (send ?a get-nombre) " no cumple todas las restricciones (" ?rs "<" ?nrest ")"  crlf)
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
    ;(printout t (send ?a get-nombre) " es optativa y todavia no se puede cursar" crlf)
    (retract ?ar)
)

(defrule descarta-especializadas "Descarta las asignaturas de especialidad si no se han superado 96 créditos ECTS"
    (refina-rec)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    ?ar <- (asig-rec (asign ?a))
    (test (< (creditos-aprobados ?al) 96))
    (test (eq Especializada (class ?a)))
    =>
    ;(printout t (send ?a get-nombre) " es especializada y todavia no se puede cursar" crlf)
    (retract ?ar)
)

(defrule fin-refina
    ?hecho1 <- (refina-rec)
    ?hecho2 <- (filtro-restr)

    =>

    (assert (agrupa))
    (retract ?hecho1 ?hecho2)
)

(defrule no-hay-asigs "Salta al módulo de presentación para informar de que no se ha encontrado solución"
    (declare (salience 2))
    ?hecho <- (agrupa)
    =>
    (bind ?facts (find-all-facts ((?a asig-rec)) TRUE))
    (if (= (length$ ?facts) 0)
        then ; no hay asigs a recomendar --> pasar a mostrar no-solucion
        (assert (no-solution))
        (retract ?hecho)
        (focus presentacion)
    )
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
    (bind ?prioridad (send ?ins get-prioridad))

    (bind ?preferente FALSE)
    (if (member asignatura-suspensa ?motivosP) then (bind ?preferente TRUE))

    (bind ?insertat FALSE)
    (loop-for-count (?i 1 (length$ ?list)) do
        (bind ?asig (nth$ ?i ?list))
        (bind ?prioridad2 (send ?asig get-prioridad))
        (if (eq ?preferente TRUE)
            then
            (bind $?list (insert$ ?list ?i ?ins))
            (bind ?insertat TRUE)
            (break)
        )
        (if (> ?prioridad ?prioridad2)
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
    ?ar <- (asig-rec (asign ?a) (motivosR $?msR) (motivosP $?msP) (rest-sat ?rs) (pref-sat ?ps) (prioridad ?p))
    ?cand <- (candidatas $?list)
    =>
    (bind ?ins (make-instance of asig-candidata (asig ?a) (motivosR ?msR) (motivosP ?msP) (grado (grado-recomendacion ?ps ?msP)) (prioridad ?p)))
    (bind $?list (subseq$ (inserta-ordenado ?ins $?list) 1 12)) ;nos quedamos con las 12 mejores candidatas

    (retract ?cand)
    (assert (candidatas ?list))

    (assert (filtra-nasig))
    (retract ?ar)
)

(defrule filtra-final "Finalización del filtrado de asignaturas candidatas"
    ?hecho <- (filtra-nasig)
    ?hecho2 <- (agrupa)
    =>
    (assert (no-solution))
    (assert (backtrack 1 (create$)))
    (assert (prefs-grupo (cumple-max_asigns FALSE) (cumple-max_horas_trabajo FALSE) (cumple-max_horas_lab FALSE)))
    (retract ?hecho)
)

(defrule backtracking "Encuentra un subconjunto de candidatas finales que cumplan correquisitos, cardinalidad y tiempos de dedicación"
    (declare (salience 1))
    ?hecho1 <- (no-solution)
    ?hecho2 <- (backtrack ?i $?grupo)
    ?cand <- (candidatas $?list)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    ?rest <- (respref (es_restriccion TRUE) (max_asigns ?ma) (max_horas_trabajo ?mht) (max_horas_lab ?mhl))
    ?pref <- (respref (es_restriccion FALSE) (max_asigns ?maP) (max_horas_trabajo ?mhtP) (max_horas_lab ?mhlP))
    ?pg <- (prefs-grupo)

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
            (bind ?as (send (nth$ ?j ?grupo) get-asig))
            (bind ?sum-horas (+ ?sum-horas (/ (- (* 25 (send ?as get-num_creditos)) (+ (send ?as get-horas_teoria) (send ?as get-horas_lab) (send ?as get-horas_prob))) 18)))
        )

        (bind ?sum-horas-lab 0)
        (loop-for-count (?j 1 (length$ ?grupo)) do
            (bind ?sum-horas-lab (+ ?sum-horas-lab (/ (send (send (nth$ ?j ?grupo) get-asig) get-horas_lab) 18) (/ (send (send (nth$ ?j ?grupo) get-asig) get-horas_prob) 18)))
        )


        (if (and (eq ?correq-ok TRUE)
                 (or (eq ?mht nil) (<= ?sum-horas ?mht))
                 (or (eq ?mhl nil) (<= ?sum-horas-lab ?mhl))) then

            ;No hay solución con ?maP asigs -> relanzamos backtracking con objetivo (?maP - 1) asigs
            (if (and (> ?maP 1) (eq ?ma nil) (= 0 (length$ ?grupo))) 
                then 
                (bind ?pref (modify ?pref (max_asigns (- ?maP 1))))
                (assert (backtrack 1 (create$)))
            )

            (if (or (and (eq ?ma nil) (= (length$ ?grupo) ?maP)) 
                    (and (neq ?ma nil) (= (length$ ?grupo) ?ma)))
                then
                (assert (horas-aut ?sum-horas))
                
                ;;; Comprobación de preferencias
                (if (and (neq nil ?maP) (= ?maP (length$ ?grupo))) then
                    (bind ?pg (modify ?pg (cumple-max_asigns TRUE)))
                )

                (if (<= ?sum-horas ?mhtP) then
                    (bind ?pg (modify ?pg (cumple-max_horas_trabajo TRUE)))
                )

                (if (<= ?sum-horas-lab ?mhlP) then
                    (bind ?pg (modify ?pg (cumple-max_horas_lab TRUE)))
                )

                (retract ?hecho1)
                (assert (solucion ?grupo))
                (focus presentacion)
            )
        )

        else
        (assert (backtrack (+ ?i 1) ?grupo))
        (bind ?asig (nth$ ?i ?list))
        (bind $?grupoCon (insert$ ?grupo (+(length$ ?grupo)1) ?asig))
        (assert (backtrack (+ ?i 1) ?grupoCon))
    )

    (retract ?hecho2)
)

(defrule solo-suspensas "Si no se ha encontrado solución y hay asignaturas suspendidas, recomendarlas"
    ?hecho1 <- (no-solution)
    ?cand <- (candidatas $?list)

    =>

    (bind $?grupo (create$))
    (loop-for-count (?i 1 (length$ ?list)) do
        (bind ?asig (nth$ ?i ?list))
        (if (member asignatura-suspensa (send ?asig get-motivosP))
            then
            (bind $?grupo (insert$ ?grupo ?i ?asig))
            else
            (break)
        )
    )
    
    (if (> (length$ ?grupo) 0)
        then
        (assert (solucion ?grupo))
        (retract ?hecho1)
    )
    (focus presentacion)
)





(defmodule presentacion "Módulo para la presentacion de resultados"
    (import MAIN ?ALL)
    (import consultas deftemplate dni)
    (import respref deftemplate respref)
    (import respref deftemplate nrestricciones)
    (import respref deftemplate preferencias)
    (import respref deffunction find-index)
    (import respref deffunction muestra-nombres-competencias)
    (import respref deffunction div-decimal)
    (import asociacion deffunction ha-aprobado)
    (import refinamiento deftemplate solucion)
    (import refinamiento deftemplate no-solution)
    (import refinamiento deftemplate candidatas)
    (import refinamiento deftemplate horas-aut)
    (import refinamiento deftemplate prefs-grupo)
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

(deffunction muestra-competencias
    ($?comp)
    
    (bind $?nombres (create$))
    (bind ?primerC TRUE)
    (loop-for-count (?i 1 (length$ ?comp)) do
        (bind ?compI (nth$ ?i ?comp))
        (bind ?nom (send ?compI get-nombre_comp))
        (bind ?ind (find-index ?nom ?nombres))
        (if (= ?ind 0)
            then ; competencia no mostrada
            (bind $?nombres (insert$ ?nombres 1 ?nom))
            
            (if (eq ?primerC FALSE) then (printout t ", "))
            (printout t (sub-string 3 (str-length ?nom) ?nom) " ")
            
            (bind $?niveles (create$))
            (loop-for-count (?j 1 (length$ ?comp)) do
                (bind ?comp-j (nth$ ?j ?comp))
                (bind ?nom-j (send ?comp-j get-nombre_comp))
                (if (= (str-compare ?nom ?nom-j) 0)
                    then
                    (bind ?niv (send ?comp-j get-nivel))
                    (bind ?insertat FALSE)
                    (loop-for-count (?k 1 (length$ ?niveles)) do
                        (if (= (str-compare ?niv (nth$ ?k ?niveles)) -1)
                            then
                            (bind $?niveles (insert$ ?niveles ?k ?niv))
                            (bind ?insertat TRUE)
                            (break)
                        )
                    )
                    (if (eq ?insertat FALSE) then (bind $?niveles (insert$ ?niveles (+(length$ ?niveles)1) ?niv)))
                )
            )
            
            (if (= (length$ ?niveles) 1) then (printout t "nivel ") else (printout t "niveles "))
            (bind ?primerN TRUE)
            (loop-for-count (?j 1 (length$ ?niveles)) do
                (if (= (length$ ?niveles) 3) then (if (eq ?j 2) then (printout t ", ")))
                (if (and (> (length$ ?niveles) 1) (eq ?j (length$ ?niveles))) then (printout t " y "))
                (bind ?niv (nth$ ?j ?niveles))
                (printout t (sub-string 2 (str-length ?niv) ?niv))
                (bind ?primerN FALSE)
            )
            
            (bind ?primerC FALSE)
        )
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
    ;(lista-motivo "Competencias" "intereses competencias" ?motivos)
    
    (bind $?comps (create$))
    (loop-for-count (?i 1 (length$ ?motivos)) do
        (bind ?mot (nth$ ?i ?motivos))
        ;(printout t ?mot "  ")
        (if (not(eq (str-index "intereses competencias" ?mot) FALSE))
            then
            (bind ?nomNiv (separa ?mot))
            
            (bind ?p1 (str-index "-" ?nomNiv))
            (bind ?nom (sub-string 1 (- ?p1 1) ?nomNiv))
            (bind ?niv (sub-string (+ ?p1 1) (str-length ?nomNiv) ?nomNiv))
            
            (bind ?comp-ins (find-instance ((?c Competencia)) (and (eq (str-compare ?c:nombre_comp ?nom) 0) (eq (str-compare ?c:nivel ?niv) 0))))
            (bind $?comps (insert$ ?comps 1 ?comp-ins))
        )
    )
    (if (> (length$ ?comps) 0)
        then
        (printout t " * Competencias: ")
        (muestra-competencias ?comps)
        (printout t crlf)
    )
)



(defrule refresc-restricciones "Muestra un sumario de las restricciones y preferencias introducidas"
    (declare (salience 10))
    (nrestricciones ?nrest ?nrest-final)
    (preferencias (prefs $?prefs))
    ?rest <- (respref (es_restriccion TRUE) (competencias_preferidas $?cp) (completar_especialidad ?ce) (max_asigns ?ma) 
                 (max_horas_trabajo ?mht) (max_horas_lab ?mhl) (tema_especializado $?te) (tipo_horario $?th))
    ?pref <- (respref (es_restriccion FALSE) (competencias_preferidas $?cpP) (completar_especialidad ?ceP) (max_asigns ?maP) 
                 (max_horas_trabajo ?mhtP) (max_horas_lab ?mhlP) (tema_especializado $?teP) (tipo_horario $?thP))
    =>
    (printout t "=====================================================================" crlf)
    (printout t "=                           Recomendacion                           =" crlf)
    (printout t "=====================================================================" crlf)
    (printout t crlf)
    
    (if (> (+ ?nrest ?nrest-final) 0)
        then
        (printout t "Restricciones aplicadas a la solucion:" crlf)
        (if (neq ?ma nil) then (printout t " * Num. asignaturas a matricular: " ?ma crlf))
        (if (neq ?mht nil) then (printout t " * Max. horas de dedicacion semanales: " ?mht crlf))
        (if (neq ?mhl nil) then (printout t " * Max. horas de laboratorio/problemas semanales: " ?mhl crlf))
        (if (eq (length$ ?th) 1) then (printout t " * Tipo de horario: " (send (nth$ 1 ?th) get-horario) crlf))
        (if (> (length$ ?te) 0) 
            then 
            (printout t " * Temas de interes: ")
            (loop-for-count (?i 1 (length$ ?te)) do
                (printout t (send (nth$ ?i ?te) get-nombre_tema))
                (if (< ?i (length$ ?te)) then (printout t ", "))
            )
            (printout t crlf)
        )
        (if (neq ?ce nil) then (printout t " * Especialidad: " (send ?ce get-nombre_esp) crlf))
        (if (> (length$ ?cp) 0) 
            then 
            (printout t " * Competencias transversales: ")
            (muestra-nombres-competencias ?cp)
        ) 
        (printout t crlf)
    )

    (if (> (length$ ?prefs) 0)
        then
        (printout t "Preferencias aplicadas a la solucion:" crlf)
        (if (member max_asigns ?prefs) then (printout t " * Num. asignaturas a matricular: " ?maP crlf))
        (if (member max_horas_trabajo ?prefs) then (printout t " * Max. horas de dedicacion semanales: " ?mhtP crlf))
        (if (member max_horas_lab ?prefs) then (printout t " * Max. horas de laboratorio/problemas semanales: " ?mhlP crlf))
        (if (member tipo_horario ?prefs) then (printout t " * Tipo de horario: " (send (nth$ 1 ?thP) get-horario) crlf))
        (if (member tema_especializado ?prefs) then 
            (printout t " * Temas de interes: ")
            (loop-for-count (?i 1 (length$ ?teP)) do
                (printout t (send (nth$ ?i ?teP) get-nombre_tema))
                (if (< ?i (length$ ?teP)) then (printout t ", "))
            )
            (printout t crlf)
        )
        (if (member completar_especialidad ?prefs) then (printout t " * Especialidad: " (send ?ceP get-nombre_esp) crlf))
        (if (member competencias_preferidas ?prefs) then 
            (printout t " * Competencias transversales: ")
            (muestra-nombres-competencias ?cpP)
        )
        (printout t crlf)
    )
)

(defrule muestra-solucion "Muestra la recomendación obtenida y más información relevante"
    (solucion $?list)
    (candidatas $?cand)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni))
    (horas-aut ?sum-horas)
    (prefs-grupo (cumple-max_asigns ?cma) (cumple-max_horas_trabajo ?cmht) (cumple-max_horas_lab ?cmhl))
    =>

    (printout t "La recomendacion del sistema consta de " (length$ ?list) " asignatura")
    (if (> (length$ ?list) 1) then (printout t "s"))
    (printout t " (")
    (if (eq ?cma FALSE) then (printout t "no "))
    (printout t "cumple preferencia), " crlf "y conllevaria los siguientes tiempos de dedicacion semanal:" crlf)
    
    (bind ?horasT 0)
    (bind ?horasLP 0)
    (loop-for-count (?i 1 (length$ ?list)) do
        (bind ?asig (nth$ ?i ?list))
        (bind ?asigI (send ?asig get-asig))
        (bind ?hT (send ?asigI get-horas_teoria))
        (bind ?hL (send ?asigI get-horas_lab))
        (bind ?hP (send ?asigI get-horas_prob))
        (bind ?horasT (+ ?horasT ?hT))
        (bind ?horasLP (+ ?horasLP ?hL ?hP))
    )
    (printout t " * Horas de dedicacion autonoma: " (div-decimal ?sum-horas 1 2) " h  (")
    (if (eq ?cmht FALSE) then (printout t "no "))
    (printout t "cumple la preferencia)" crlf)
    (printout t " * Horas de laboratorio/problemas: " (div-decimal ?horasLP 18 2) " h  (")
    (if (eq ?cmhl FALSE) then (printout t "no "))
    (printout t "cumple la preferencia)" crlf)
    (printout t crlf crlf)
    
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
    
    (bind $?resto (create$))
    (loop-for-count (?i 1 (length ?cand)) do
        (if (not(member (nth$ ?i ?cand) ?list))
            then
            (bind $?resto (insert$ ?resto (+(length$ ?resto)1) (nth$ ?i ?cand)))
        )
    )
    
    (if (> (length$ ?resto) 0)
        then
        (printout t "El sistema tambien encontro las siguientes asignaturas para recomendar:" crlf)
        (bind ?primer TRUE)
        (loop-for-count (?i 1 (length$ ?resto)) do
            (bind ?asig (nth$ ?i ?resto))
            (bind ?asigI (send ?asig get-asig))

            ;Comprobación de correquisitos
            (bind ?correquisitos (send ?asigI get-correquisitos))
            (bind ?correq-ok TRUE)
            (loop-for-count (?k 1 (length$ ?correquisitos)) do
                (if (not (or (ha-aprobado ?al (nth$ ?k ?correquisitos)) (member (nth$ ?k ?correquisitos) ?resto))) then
                    (bind ?correq-ok FALSE)
                    (break)
                )
            )

            (if (eq ?correq-ok TRUE) then
                (bind ?nomA (send ?asigI get-nombre))
                (if (eq ?primer FALSE) then (printout t ", "))
                (printout t ?nomA)
                (bind ?primer FALSE)
            )
        )
        (printout t crlf crlf)
    )
)

(defrule no-solucion "Muestra un mensaje informando que no se ha encontrado solución"
    (no-solution)
    =>
    (printout t "El sistema no ha encontrado una solucion acorde a sus restricciones/preferencias" crlf)
    (printout t crlf)
)