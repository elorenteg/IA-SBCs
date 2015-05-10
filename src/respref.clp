;;
;; Estructuras para la recogida de datos de restricciones/preferencias
;;

(deftemplate respref
    (slot es_restriccion)
    (multislot competencias_preferidas)
    (slot completar_especialidad)
    (slot dificultad (allowed-strings "facil" "dificil"))
    (slot max_asigns (range 0 1)) ;max 36 ECTS/cuatri --> con una asignatura 6 ECTS, son 6 asigs.
    (slot max_horas_trabajo) ;max 36 ECTS/cuatri y 1ECTS=25h --> 900h
    (slot max_horas_lab)
    (multislot tema_especializado (default (create$)))
    (multislot tipo_horario (cardinality 1 2) (default (create$)))
)

(defrule entrada-respref "Pide las preferencias y las restricciones"
    (dni ?dni)
    =>
    (printout t "Entrada de restricciones/preferencias" crlf)
	(assert (ent-respref FALSE))
    (assert (ent-respref TRUE))
    (assert (respref (es_restriccion TRUE)))
    (assert (respref (es_restriccion FALSE)))
)

(defrule preguntas-respref "Modifica los hechos de ResPref segun lo que pida el alumno"
    ?hecho <- (ent-respref ?es-rest)
	(dni ?dni)
	?alumn <- (object (is-a Alumno) (id ?dni))  ; ?alumn es la instancia del alumno con id ?dni al que le queremos introducir las respref
    ?rec <- (respref (es_restriccion ?es-rest) (tipo_horario $?tipo-horario) (tema_especializado $?temasI))
    
	=>
    
	(if (eq ?es-rest TRUE)
		then
		(progn (format t ">> Restricciones%n") (assert (restrs ok)))
		else
		(progn (format t ">> Preferencias%n") (assert (prefs ok)))
	)

    (bind ?ma (pregunta-rango ">> Cual es el numero maximo de asignaturas a matricular?" TRUE 1 6))
    (if (not(eq ?ma nil))
        then
        (bind ?rec (modify ?rec (max_asigns ?ma)))
    )

    (bind ?mh (pregunta-rango ">> Cual es el numero maximo de horas de dedicacion semanales?" TRUE 0 900))
    (if (not(eq ?mh nil))
        then
        (bind ?rec (modify ?rec (max_horas_trabajo ?mh)))
    )

    (bind ?ml (pregunta-rango ">> Cual es el numero maximo de horas de laboratorio semanales?" TRUE 0 900))
    (if (not(eq ?ml nil))
        then
        (bind ?rec (modify ?rec (max_horas_lab ?ml)))
    )

    (bind ?th (pregunta-cerrada ">> Que horario se ajusta mejor a su disponibilidad?" TRUE manyana tarde))
	(if (not(eq ?th nil))
        then
        (bind ?th-ins (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus ?th))))
        (bind ?rec (modify ?rec (tipo_horario ?th-ins)))
        else
        (bind ?th-ins-man (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus "manyana"))))
        (bind ?th-ins-tar (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus "tarde"))))
        (bind ?tipo-horario (insert$ ?tipo-horario 1 ?th-ins-man))
        (bind ?tipo-horario (insert$ ?tipo-horario 2 ?th-ins-tar))
        (bind ?rec (modify ?rec (tipo_horario ?tipo-horario)))
    )
    
    (bind ?temasN (create$))
    (do-for-all-instances ((?t Especializado)) TRUE (bind ?e (insert$ ?temasN 1 (send ?t get-nombre_tema))))
    (bind ?ti (pregunta-cerrada ">> Que temas especializados te interesan?" TRUE ?temasN)) ; NO acaba de pillar bien la entrada de nombres!! ;
    (printout t "temas" $?ti crlf)
    (if (not(eq ?ti nil))
        then
        (bind ?i 1)
        (while (<= ?i (length$ ?ti))
            do
                (bind ?t (nth$ ?i ?ti))
                (bind ?tema-ins (find-instance ((?ti Especializado)) (eq ?ti:nombre_tema ?t)))
                (bind ?temasI (insert$ ?temasI 1 ?tema-ins))
                (bind ?rec (modify ?rec (tema_especializado ?temasI)))
                (bind ?i (+ ?i 1))
        )
    )
    
    (bind ?espN (create$))
    (do-for-all-instances ((?t Especialidad)) TRUE (bind ?espN (insert$ ?espN 1 (send ?t get-nombre_esp))))
    (bind ?ei (pregunta-cerrada ">> Que especialidad deseas acabar?" TRUE ?espN)) ; NO acaba de pillar bien la entrada de nombres!! ;
    (printout t "especialidades " $?ei crlf)
    (if (not(eq ?ei nil))
        then
        (bind ?i 1)
        (while (<= ?i (length$ ?ei))
            do
                (bind ?t (nth$ ?i ?ei))
                (bind ?esp-ins (find-instance ((?ei Especialidad)) (eq ?ei:nombre_esp ?t)))
                (bind ?espI (insert$ ?espI 1 ?esp-ins))
                (bind ?rec (modify ?rec (tema_especializado ?espI)))
                (bind ?i (+ ?i 1))
        )
    )
    
    (bind ?di (pregunta-cerrada ">> Que dificultat puedes asumir?" TRUE facil dificil))
	(if (not(eq ?th nil))
        then
        (bind ?rec (modify ?rec (dificultad ?di)))
    )
    
    (bind ?comP (create$))
    (do-for-all-instances ((?t Competencia)) TRUE (bind ?comP (insert$ ?comP 1 (send ?t get-nombre_comp))))
    (bind ?cp (pregunta-cerrada ">> Cuales son tus competencias favoritas?" TRUE ?comP)) ; NO acaba de pillar bien la entrada de nombres!! ;
    (printout t "competencias " $?cp crlf)
    (if (not(eq ?cp nil))
        then
        (bind ?i 1)
        (while (<= ?i (length$ ?cp))
            do
                (bind ?t (nth$ ?i ?cp))
                (bind ?comp-ins (find-instance ((?cp Competencia)) (eq ?cp:nombre_comp ?t)))
                (bind ?compI (insert$ ?compI 1 ?comp-ins))
                (bind ?rec (modify ?rec (tema_especializado ?compI)))
                (bind ?i (+ ?i 1))
        )
    )
    
	;;; TODO: añadir mas preguntas de ResPref ;;;
    
    (retract ?hecho)
)

(defrule entrada-inferencia "Infiere restricciones/preferencias segun el expediente"
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni))
    ?rest <- (respref (es_restriccion TRUE))
    ?pref <- (respref (es_restriccion FALSE))
    ?hecho1 <- (prefs ok)
    ?hecho2 <- (restrs ok)
    =>
    
    ;;; TODO: inferencia de respref ;;;
    (printout t "Inferencia de restricciones/preferencias" crlf)
    
    (assert(inferencia ok))
    (retract ?hecho1)
    (retract ?hecho2)
)