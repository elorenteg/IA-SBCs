;;
;; Estructuras para la recogida de datos de restricciones/preferencias
;;

(deftemplate respref
    (slot es_restriccion)
    (multislot competencias_preferidas)
    (slot completar_especialidad)
    (slot dificultad (allowed-strings "facil" "dificil"))
    (slot max_asigns (type INTEGER) (range 0 6)) ;max 36 ECTS/cuatri --> con una asignatura 6 ECTS, son 6 asigs.
    (slot max_horas_trabajo (type INTEGER) (range 0 900)) ;max 36 ECTS/cuatri y 1ECTS=25h --> 900h
    (slot max_horas_lab (type INTEGER) (range 0 900))
    (multislot tema_especializado)
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
    ?rec <- (respref (es_restriccion ?es-rest) (tipo_horario $?tipo-horario))
    
	=>
    
	(if (eq ?es-rest TRUE)
		then
		(progn (format t ">> Restricciones%n") (assert (restrs ok)))
		else
		(progn (format t ">> Preferencias%n") (assert (prefs ok)))
	)

    (bind ?ma (pregunta-rango ">> Cual es el numero maximo de asignaturas a matricular?" TRUE 1 8))
    (if (not(eq ?ma nil))
        then
        (bind ?rec (modify ?rec (max_asigns ?ma)))
    )

    (bind ?mh (pregunta-rango ">> Cual es el numero maximo de horas de dedicacion semanales?" TRUE 0 100))
    (if (not(eq ?mh nil))
        then
        (bind ?rec (modify ?rec (max_horas_trabajo ?mh)))
    )

    (bind ?ml (pregunta-rango ">> Cual es el numero maximo de horas de laboratorio semanales?" TRUE 0 100))
    (if (not(eq ?ml nil))
        then
        (bind ?rec (modify ?rec (max_horas_lab ?ml)))
    )

    (bind ?th (pregunta-cerrada ">> Que horario se ajusta mejor a su disponibilidad?" TRUE manyana tarde cualquiera))
	(if (not(eq ?th nil))
        then
        (if (or (=(str-compare ?th "manyana")0) (=(str-compare ?th "tarde")0))
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