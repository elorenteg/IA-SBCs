;;
;; Estructuras para la asociacion heuristica de un problema abstracto a una solucion abstracta
;;

(deftemplate asig-rec "Asignatura recomendada con sus motivos (a partir de todas las reglas)"
    (slot asign)
    (multislot motivos (default (create$)))
    (slot rest-sat) ;número de restricciones que satisface
    (slot pref-sat) ;número de preferencias que satisface
    ;añadir también el grado de recomendación? [altamente recomendable, recomendable]
)

(deftemplate solucion-abstracta "Asignaturas recomendadas" ; ya no es necesario (?)
    (multislot list-asigns (default (create$)))
)

(deftemplate nueva-rec "Nueva asignatura recomendada por una regla"
    (slot asign)
    (slot motivo)
    (slot es-pref)
)

(defrule modifica-asig-rec "Modifica una asignatura recomendada (añade motivo y/o pref-sat)"
    (declare (salience 10)) ;tiene prioridad para comprobar si ya existe la asig-rec
    ?nr <- (nueva-rec (asign ?a) (motivo ?m) (es-pref ?ep))
    ?ar <- (asig-rec (asign ?a) (motivos $?ms) (rest-sat ?rs) (pref-sat ?ps))
    =>
    (if (eq ?ep TRUE)
        then
        (bind ?ps-nuevo (+ 1 ?ps))
        (bind ?rs-nuevo ?rs)
        else
        (bind ?ps-nuevo ?ps)
        (bind ?rs-nuevo (+ 1 ?rs))
    )
    (bind ?ar (modify ?ar (motivos (insert$ ?ms 1 ?m)) (rest-sat ?rs-nuevo) (pref-sat ?ps-nuevo)))

    (retract ?nr)
)

(defrule anade-asig-rec "Añade una nueva asignatura recomendada (antes no existía)"
    ?nr <- (nueva-rec (asign ?a) (motivo ?m) (es-pref ?ep))
    (not (exists (asig-rec (asign ?a))))
    =>
    (if (eq ?ep TRUE)
        then
        (bind ?ps 1)
        (bind ?rs 0)
        else
        (bind ?ps 0)
        (bind ?rs 1)
    )
    (assert (asig-rec (asign ?a) (motivos (create$ ?m)) (rest-sat ?rs) (pref-sat ?ps)))

    (retract ?nr)
)


(defrule entrada-asociacion "Asociacion heuristica del problema"
    ?hecho <- (abstraccion ok)
    =>
    ;;; TODO: asociacion del problema ;;;
    (printout t "Asociacion del problema" crlf)

    (assert (solucion-abstracta (list-asigns (create$))))
    (assert(ent-asigs))
    (retract ?hecho)
)

(defrule escoge-horario-preferido
    (asigs ok)
    ?prob-abs <- (problema-abstracto (horario-preferidoR ?td)) ;si añado "(horario-preferidoP ?tdP)", no entrará a menos el usuario haya introducido ambos criterios
    =>
    ;Restricciones
    (bind ?res (create$))
    (bind ?ins-asigs (find-all-instances ((?ins Asignatura))
        (member ?td (create$ (progn$ (?cand (send ?ins get-horarios)) (insert$ ?res (+ 1 (length$ ?res)) (send ?cand get-horario)))))
    ))

    (loop-for-count (?i 1 (length$ ?ins-asigs)) do
        (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo horario-preferido) (es-pref FALSE))) ;poner un motivo más user-friendly
    )

    ;Preferencias
    ;(bind ?resP (create$))
    ;(bind ?ins-asigsP (find-all-instances ((?ins Asignatura))
    ;    (member ?tdP (create$ (progn$ (?cand (send ?ins get-horarios)) (insert$ ?resP (+ 1 (length$ ?resP)) (send ?cand get-horario)))))
    ;))

    ;(loop-for-count (?i 1 (length$ ?ins-asigsP)) do
    ;    (assert (nueva-rec (asign (nth$ ?i ?ins-asigsP)) (motivo horario-preferido) (es-pref TRUE))) ;poner un motivo más user-friendly
    ;)
)

(defrule escoge-volumen-trabajo
    (asigs ok)
    ?prob-abs <- (problema-abstracto (volumen-trabajoR ?vt))

    =>

    (if (eq ?vt bajo)
        then
        (bind ?min 0)
        (bind ?max 27)
        else (if (eq ?vt medio)
            then
            (bind ?min 28)
            (bind ?max 37)
            else
            (bind ?min 37)
            (bind ?max 100)
        )
    )

    ;Restricciones
    (bind ?ins-asigs (find-all-instances ((?ins Asignatura))
        (and
            (<= ?min (+ (send ?ins get-horas_lab) (send ?ins get-horas_prob)))
            (<= (+ (send ?ins get-horas_lab) (send ?ins get-horas_prob)) ?max))))

    (loop-for-count (?i 1 (length$ ?ins-asigs)) do
        (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo volumen-trabajo) (es-pref FALSE))) ;poner un motivo más user-friendly
    )
)


(defrule escoge-interes-compl-esp
    (asigs ok)
    ?prob-abs <- (problema-abstracto (interes-compl-espR ?ice))
    ?al <- (object (is-a Alumno) (id ?dni) (especialidad ?e))
    =>
    (bind ?ins-asigs (find-all-instances ((?ins Especializada)) (member ?e ?ins:especialidad_asig)))

    (if (eq ?ice alto)
        then
        (loop-for-count (?i 1 (length$ ?ins-asigs)) do
            (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo interes-compl-esp) (es-pref FALSE))) ;poner un motivo más user-friendly
        )
        ;qué pasa si tiene interés "medio"?
        ;y si tiene interés "ninguno", impedimos la recomendación de asigs. de especialidad?
    )

)

(defrule escoge-asigns
    ?hecho <- (ent-asigs)
    ?abs <- (problema-abstracto)
    =>

    ;;; TODO: mirar las asignaturas y escoger segun el problema abstracto ;;;

    (assert (asigs ok))
    (retract ?hecho)
)

(defrule fin-asociacion "Comprueba que se ejecuten todas las reglas de Asociacion"
    ?hecho1 <- (asigs ok)
    =>
    ;;; esta regla elimina los hechos usados en la asociacion y genera un assert conforme ha acabado ;;;
    (printout t "Fin asociacion" crlf)
    (assert(asociacion ok))
    (retract ?hecho1)
)
