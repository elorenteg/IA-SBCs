;;
;; Estructuras para consultar información del usuario
;;


(deffunction pregunta
    (?pregunta ?puede-omitir)

    (if ?puede-omitir then (bind ?salida-opc "(opcional)")
    else (bind ?salida-opc ""))

    (format t ">> %s %s " ?pregunta ?salida-opc)
    (bind ?respuesta (lowcase (read)))

    (if (and (eq ?respuesta -) ?puede-omitir) then (return nil)) ;permite omitir la pregunta
    ?respuesta
)

(deffunction pregunta-rango
    (?pregunta ?puede-omitir ?min ?max)

    (if ?puede-omitir then (bind ?salida-opc "(opcional)")
    else (bind ?salida-opc ""))

    (format t ">> %s [%d, %d] %s " ?pregunta ?min ?max ?salida-opc)
    (bind ?respuesta (read))

    (if (and (eq ?respuesta -) ?puede-omitir) then (return nil)) ;permite omitir la pregunta
    (while (or (< ?respuesta ?min) (> ?respuesta ?max))
        (printout t "No se ha introducido una respuesta valida" crlf)
        (format t ">> %s [%d, %d] %s " ?pregunta ?min ?max ?salida-opc)
        (bind ?respuesta (read))
    )
    ?respuesta
)

(deffunction pregunta-cerrada
    (?pregunta ?puede-omitir $?candidatos)

    (if ?puede-omitir then (bind ?salida-opc "(opcional)")
    else (bind ?salida-opc ""))

    (progn$ (?var ?candidatos) (lowcase ?var))
    (format t ">> %s [%s] %s " ?pregunta (implode$ ?candidatos) ?salida-opc)
    (bind ?respuesta (read))

    (if (and (eq ?respuesta -) ?puede-omitir) then (return nil)) ;permite omitir la pregunta
    (while (not (member (lowcase ?respuesta) ?candidatos)) do
        (printout t "No se ha introducido una respuesta valida" crlf)
        (format t ">> %s [%s] %s " ?pregunta (implode$ ?candidatos) ?salida-opc)
        (bind ?respuesta (read))
    )
    ?respuesta
)

(deffunction pregunta-binaria
    (?pregunta ?puede-omitir)

    (bind ?respuesta (pregunta-cerrada ?pregunta ?puede-omitir si no s n))
    (if (and (eq ?respuesta -) ?puede-omitir) then (return nil)) ;permite omitir la pregunta

    (if (or (eq (lowcase ?respuesta) si) (eq (lowcase ?respuesta) s))
        then TRUE
        else FALSE
    )
)

(deffunction existe-alumno "Consulta si existe un alumno con cierto DNI"
    (?dni)

    (bind ?l (find-all-instances ((?a Alumno)) (= ?a:id ?dni)))
    (if (= (length$ ?l) 1)
        then TRUE
        else FALSE
    )
)

(deffunction primera-mayus "Convierte un string para que la primera letra sea mayúscula"
    (?str)

    (str-cat (upcase (sub-string 0 1 ?str)) (sub-string 2 (length$ ?str) ?str))
)

(deffunction resprefs-alumno "Devuelve el conjunto de restricciones y preferencias de un alumno"
    (?dni)

    (bind ?al (find-instance ((?a Alumno)) (= ?a:id ?dni)))
    (if (!= (length$ ?al) 1) then (return nil) else (send (eval (implode$ ?al)) get-respref_alumno))
)

(deffunction muestra-resprefs "Muestra por pantalla las restricciones y preferencias de un alumno"
    (?dni)

    (bind ?resprefs (resprefs-alumno ?dni))
    (loop-for-count (?i 1 (length$ ?resprefs)) do
        (printout t "#" ?i ":" crlf)
        (send (nth$ ?i ?resprefs) print)
        (printout t crlf)
    )
)

(deffunction muestra-convocatorias-alumno "Muestra las convocatorias a las que se ha presentado un alumno"
    (?dni)

    (bind ?al (find-instance ((?a Alumno)) (= ?a:id ?dni))) ;falta comprobar si existe el alumno
    (bind ?exp (send (eval (implode$ ?al)) get-expediente_alumno))
    (bind ?notas (send ?exp get-notas_exp)) ;todas las notas del alumno
    (progn$ (?ins ?notas) (printout t (send (send ?ins get-convocatoria_nota) print) crlf))
)

;;; TODO: organizar reglas de "consulta al usuario" bajo un mismo módulo ;;;

(defrule main
    (initial-fact)
    =>
    (format t ">> Iniciando Sistema de Recomendacion de Matricula de la FIB%n")
    (assert (bienvenida ok))
)

(defrule entrada-alumno
    (bienvenida ok)
    =>
    (bind ?dni (pregunta-rango "Introduzca su identificador (DNI):" FALSE 0 9999))
    (if (not (existe-alumno ?dni))
         then
         (printout t "Alumno nuevo creado con identificador " ?dni crlf)
         (make-instance (sym-cat alumno- (gensym)) of Alumno (id ?dni))
		 ;;; TODO: pedir mas datos del alumno ;;;
         else
         (format t "Alumno ya dentro del sistema%n")
		 ;;; TODO: imprimir datos del alumno ;;;
    )
    (assert (e-dni ok))
    (assert (dni ?dni))
)


;;; RESPREF
(deftemplate respref
    (slot es_restriccion (allowed-strings "TRUE" "FALSE"))
    (multislot competencias_preferidas)
    (slot completar_especialidad (allowed-strings "TRUE" "FALSE"))
    (slot dificultad (allowed-strings "facil" "dificil"))
    (slot max_asigns (type INTEGER) (range 0 6)) ;max 36 ECTS/cuatri --> con una asignatura 6 ECTS, son 6 asigs.
    (slot max_horas_trabajo (type INTEGER) (range 0 900)) ;max 36 ECTS/cuatri y 1ECTS=25h --> 900h
    (slot max_horas_lab (type INTEGER) (range 0 900))
    (multislot tema_especializado)
    (multislot tipo_horario (allowed-strings "manyana" "tarde") (cardinality 1 2))
)

(defrule entrada-respref "Genera instancias de ResPref segun lo que pida diga el alumno"
    ?hecho <- (ent-respref ?es-rest)
	(dni ?dni)
	?alumn <- (object (is-a Alumno) (id ?dni))  ; ?alumn es la instancia del alumno con id ?dni al que le queremos introducir las respref
    ?rec <- (respref (es_restriccion ?es-rest))
    
	=>
    
	(if (eq ?es-rest TRUE)
		then
		(progn (format t ">> Entrada de Preferencias%n") (assert (prefs ok)))
		else
		(progn (format t ">> Entrada de Restricciones%n") (assert (restrs ok)))
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

    (bind ?th (pregunta-cerrada ">> Que horario se ajusta mejor a su disponibilidad?" TRUE manyana tarde))
	(if (not(eq ?th nil))
         then
		 ;(bind ?th-ins (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus ?th))))
         ;(bind ?thI (make-instance (sym-cat respref-th- (gensym)) of Tipo_Horario (es_preferencia ?es-pref) (tipo_horario ?th-ins)))
		 ;(slot-insert$ ?alumn respref_alumno 1 ?thI)
         (bind ?rec (modify ?rec (tipo_horario ?th)))
    )
    
	;;; TODO: añadir mas preguntas de ResPref ;;;
    
    (retract ?hecho)
)

(defrule resfref "Pide las preferencias y las restricciones"
    (e-dni ok) (dni ?dni)
    =>
	(assert (ent-respref FALSE))
    (assert (ent-respref TRUE))
    (assert (respref (es_restriccion TRUE)))
    (assert (respref (es_restriccion FALSE)))
)

(defrule check "Prueba para mostrar resprefs"
    (prefs ok)
    (restrs ok)
    (dni ?dni)
    =>
    (muestra-resprefs ?dni)
)
