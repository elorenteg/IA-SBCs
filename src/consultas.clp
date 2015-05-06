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
    ?hecho <- (initial-fact)
    =>
    (format t ">> Iniciando Sistema de Recomendacion de Matricula de la FIB%n")
    (assert (bienvenida ok))
    (retract ?hecho)
)

(defrule entrada-alumno
    ?hecho <- (bienvenida ok)
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
    (assert (dni ?dni))
    (retract ?hecho)
)