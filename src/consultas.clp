;;
;; Estructuras para consultar información del usuario
;;


(deffunction pregunta
    (?pregunta)

    (format t ">> %s? " ?pregunta)
    (bind ?respuesta (lowcase (read)))
    ?respuesta
)

;;; TODO: indicar por la salida si una pregunta es opcional ;;;
(deffunction pregunta-rango
    (?pregunta ?puede-omitir ?min ?max)

    (format t ">> %s [%d, %d] " ?pregunta ?min ?max)
    (bind ?respuesta (read))
    (if (and (eq ?respuesta -) ?puede-omitir) then (return nil)) ;permite omitir la pregunta
    (while (or (< ?respuesta ?min) (> ?respuesta ?max))
        (printout t "No se ha introducido una respuesta valida" crlf)
        (format t ">> %s " ?pregunta)
        (bind ?respuesta (read))
    )
    ?respuesta
)

(deffunction pregunta-cerrada
    (?pregunta $?candidatos)

    (progn$ (?var ?candidatos) (lowcase ?var))
    (format t ">> %s (%s) " ?pregunta (implode$ ?candidatos))
    (bind ?respuesta (read))
    (while (not (member (lowcase ?respuesta) ?candidatos)) do
        (printout t "No se ha introducido una respuesta valida" crlf)
        (format t ">> %s (%s) " ?pregunta (implode$ ?candidatos))
        (bind ?respuesta (read))
    )
    ?respuesta
)

(deffunction pregunta-binaria
    (?pregunta)

    (bind ?respuesta (pregunta-cerrada ?pregunta si no s n))
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

;;; TODO: organizar reglas de "consulta al usuario" bajo un mismo módulo ;;;
;;; TODO: mostrar pantalla de bienvenida antes de las preguntas ;;;

(defrule entrada-alumno
    (initial-fact)
    =>
    (bind ?dni (pregunta-rango "Introduzca su identificador (DNI):" FALSE 0 9999))
    (while (not (existe-alumno ?dni)) do
        (printout t "No existe ningun alumno con identificador " ?dni crlf)
        (bind ?dni (pregunta-rango "Introduzca su identificador (DNI):" FALSE 0 9999))
    )
    (assert (e-dni ok))
    (assert (dni ?dni))
)

(defrule entrada-max-asigs
    (e-dni ok)
    =>
    (bind ?ma (pregunta-rango "Cual es el numero maximo de asignaturas a matricular?" TRUE 1 8))
    (assert (e-max-asigs ok)) ;;; TODO: almacenar en una nueva instancia de ResPref ;;;
    (assert (max-asigs ?ma))
)

(defrule entrada-max-horas
    (e-dni ok)
    =>
    (bind ?mh (pregunta-rango "Cual es el numero maximo de horas de dedicacion semanales ?" TRUE 0 100))
    (assert (e-max-horas ok)) ;;; TODO: almacenar en una nueva instancia de ResPref ;;;
    (assert (max-horas ?mh))
)
