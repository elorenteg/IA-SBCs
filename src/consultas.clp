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

(defrule entrada-max-asigs
    (e-dni ok) (no-match 0)
    =>
    (bind ?ma (pregunta-rango "Cual es el numero maximo de asignaturas a matricular?" TRUE 1 8))
    (assert (e-max-asigs ok)) ;;; TODO: almacenar en una nueva instancia de ResPref ;;;
    (assert (max-asigs ?ma))
)

(defrule entrada-max-horas
    (e-dni ok) (no-match 0)
    =>
    (bind ?mh (pregunta-rango "Cual es el numero maximo de horas de dedicacion semanales ?" TRUE 0 100))
    (assert (e-max-horas ok)) ;;; TODO: almacenar en una nueva instancia de ResPref ;;;
    (assert (max-horas ?mh))
)


;;; RESPREF

(deffunction entrada-respref "Genera instancias de ResPref segun lo que pida diga el alumno"
    (?es-pref)

    (bind ?ma (pregunta-rango ">> Cual es el numero maximo de asignaturas a matricular?" TRUE 1 8))
    (make-instance (sym-cat respref-ma- (gensym)) of Max_Asignaturas (es_preferencia ?es-pref) (max_asigns ?ma))
    (bind ?mh (pregunta-rango ">> Cual es el numero maximo de horas de dedicacion semanales?" TRUE 0 100))
    (make-instance (sym-cat respref-mh- (gensym)) of Max_Horas_Trabajo (es_preferencia ?es-pref) (max_horas_trabajo ?mh))
    (bind ?ml (pregunta-rango ">> Cual es el numero maximo de horas de laboratorio semanales?" TRUE 0 100))
    (make-instance (sym-cat respref-ml- (gensym)) of Max_Horas_Lab (es_preferencia ?es-pref) (max_horas_lab ?ml))

    (bind ?th (pregunta-cerrada ">> Que horario se ajusta mejor a su disponibilidad?" TRUE manyana tarde))
    (bind ?th-may (primera-mayus ?th))
    (bind ?x (find-instance ((?ins Horario)) (eq ?ins:horario ?th-may))) ;no reconocerá el horario "Manyana"...
    (make-instance (sym-cat respref-th- (gensym)) of Tipo_Horario (es_preferencia ?es-pref) (tipo_horario ?th))
	;;; TODO: añadir mas preguntas de ResPref ;;;
)

(defrule resfref "Pide las preferencias y las restricciones"
    (e-dni ok)
    =>
    (format t ">> Entrada de Preferencias%n")
    (entrada-respref TRUE)
    (format t ">> Entrada de Restricciones%n")
    (entrada-respref FALSE)
    (assert (recomm ok))
)

