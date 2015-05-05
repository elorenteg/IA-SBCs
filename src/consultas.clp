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

(defrule entrada-respref "Genera instancias de ResPref segun lo que pida diga el alumno"
    (ent-respref ?es-pref)
	(dni ?dni)
	?alumn <- (object (is-a Alumno) (id ?dni))  ; ?alumn es la instancia del alumno con id ?dni al que le queremos introducir las respref
	
	=>
	
	(printout t "facts en memoria " (facts) crlf)
	
	(if (eq ?es-pref TRUE)
		then
		(format t ">> Entrada de Preferencias%n")
		else
		(format t ">> Entrada de Restricciones%n")
	)
	(send ?alumn put-id 10) ; formato para cambiar un slot de una instancia
	(printout t "prueba " (send ?alumn get-id) crlf) ; formato para obtener el valor de un slot de una instancia

    (bind ?ma (pregunta-rango ">> Cual es el numero maximo de asignaturas a matricular?" TRUE 1 8))
    (if (not(eq ?ma nil))
         then
         (bind ?maI (make-instance (sym-cat respref-ma- (gensym)) of Max_Asignaturas (es_preferencia ?es-pref) (max_asigns ?ma)))
		 (slot-insert$ ?alumn respref_alumno 1 ?maI)
    )
	
    (bind ?mh (pregunta-rango ">> Cual es el numero maximo de horas de dedicacion semanales?" TRUE 0 100))
    (if (not(eq ?mh nil))
         then
         (bind ?mhI (make-instance (sym-cat respref-mh- (gensym)) of Max_Horas_Trabajo (es_preferencia ?es-pref) (max_horas_trabajo ?mh)))
		 (slot-insert$ ?alumn respref_alumno 1 ?mhI)
    )
	
    (bind ?ml (pregunta-rango ">> Cual es el numero maximo de horas de laboratorio semanales?" TRUE 0 100))
    (if (not(eq ?ml nil))
         then
         (bind ?mlI (make-instance (sym-cat respref-ml- (gensym)) of Max_Horas_Lab (es_preferencia ?es-pref) (max_horas_lab ?ml)))
		 (slot-insert$ ?alumn respref_alumno 1 ?mlI)
    )

    (bind ?th (pregunta-cerrada ">> Que horario se ajusta mejor a su disponibilidad?" TRUE manyana tarde))
	(if (not(eq ?th nil))
         then
		 (bind ?th-ins (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus ?th))))
         (bind ?thI (make-instance (sym-cat respref-th- (gensym)) of Tipo_Horario (es_preferencia ?es-pref) (tipo_horario ?th-ins)))
		 (slot-insert$ ?alumn respref_alumno 1 ?thI)
    )
	;;; TODO: añadir mas preguntas de ResPref ;;;
)

(defrule resfref "Pide las preferencias y las restricciones"
    (e-dni ok) (dni ?dni)
    =>
	(assert (ent-respref TRUE))
	(assert (ent-respref FALSE))
)

