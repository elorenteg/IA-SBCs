;;
;; Estructuras para consultar información del usuario
;;

(defrule inicio
    (initial-fact)
    =>
    (focus consultas)
)


(defmodule consultas "Módulo para consultar información del usuario"
    (import MAIN ?ALL)
    (export ?ALL)
)


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

(deffunction pregunta-numero
    (?pregunta ?puede-omitir $?candidatos)

    (if ?puede-omitir then (bind ?salida-opc "(opcional)")
    else (bind ?salida-opc ""))

    (format t ">> %s %s %n" ?pregunta ?salida-opc)
    (loop-for-count (?i 1 (length$ ?candidatos)) do
        (bind ?cand (nth$ ?i ?candidatos))
        (format t "  (%d) %s%n" ?i ?cand)
    )
    
    (bind ?min 1)
    (bind ?max (length$ ?candidatos))
    
    (bind ?respuesta (read))
    (if (and (eq ?respuesta -) ?puede-omitir) then (return nil)) ;permite omitir la pregunta
    (while (or (< ?respuesta ?min) (> ?respuesta ?max))
        (printout t "No se ha introducido una respuesta valida" crlf)
        (format t ">> %s [%d, %d] %s " ?pregunta ?min ?max ?salida-opc)
        (bind ?respuesta (read))
        (if (and (eq ?respuesta -) ?puede-omitir) then (return nil)) ;permite omitir la pregunta
    )
    
    ?respuesta
)

(deffunction fuera-rango
    (?min ?max $?lista-res)

    (loop-for-count (?i 1 (length$ ?lista-res)) do
        (bind ?res (nth$ ?i ?lista-res))
        (if (or (< ?res ?min) (> ?res ?max))
            then
            (return TRUE)
        )
    )
    
    (return FALSE)
)

(deffunction pregunta-lista-numeros
    (?pregunta ?puede-omitir $?candidatos)

    (if ?puede-omitir then (bind ?salida-opc "(opcional)")
    else (bind ?salida-opc ""))

    (format t ">> %s %s %n" ?pregunta ?salida-opc)
    (loop-for-count (?i 1 (length$ ?candidatos)) do
        (bind ?cand (nth$ ?i ?candidatos))
        (format t "  (%d) %s%n" ?i ?cand)
    )
    
    (bind ?min 1)
    (bind ?max (length$ ?candidatos))
    
    (bind ?respuesta (readline))
    (if (and (eq ?respuesta "-") ?puede-omitir) then (return nil)) ;permite omitir la pregunta
    (bind $?lista-res (str-explode ?respuesta))
    (while (fuera-rango ?min ?max ?lista-res)
        (printout t "No se ha introducido una respuesta valida" crlf)
        (format t ">> %s [%d, %d] %s " ?pregunta ?min ?max ?salida-opc)
        (bind ?respuesta (readline))
        (if (and (eq ?respuesta "-") ?puede-omitir) then (return nil)) ;permite omitir la pregunta
        (bind $?lista-res (str-explode ?respuesta))
    )
    
    $?lista-res
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
    ?hecho <- (initial-fact)
    =>
    
    (printout t "=====================================================================" crlf)
    (printout t "=         Sistema de recomendacion de asignaturas de la FIB         =" crlf)
    (printout t "=====================================================================" crlf)
    (printout t crlf)
    (assert (bienvenida ok))
    (retract ?hecho)
)

(defrule entrada-alumno
    ?hecho <- (bienvenida ok)
    =>
    (bind ?dni (pregunta-rango "Introduzca su identificador (DNI):" FALSE 0 9999))
    (while (not (existe-alumno ?dni)) do
        (printout t "No existe ningun alumno con identificador " ?dni crlf)
        (bind ?dni (pregunta-rango "Introduzca su identificador (DNI):" FALSE 0 9999))
    )
    (printout t crlf)
    
    (assert (dni ?dni))
    (retract ?hecho)

    (focus respref)
)