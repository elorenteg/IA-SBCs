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

(deftemplate nueva-rec "Nueva asignatura recomendada por una regla"
    (slot asign)
    (slot motivo)
    (slot es-pref)
)

(deffunction interseccion-vacia "Indica si la intersección de dos listas (como conjuntos) está vacía"
    (?L1 ?L2)

    (loop-for-count  (?i 1 (length$ ?L1)) do
        (if (member (nth$ ?i ?L1) ?L2) then (return FALSE))
    )
    (return TRUE)
)




(defrule entrada-asociacion "Asociacion heuristica del problema"
    ?hecho <- (abstraccion ok)
    =>
    (printout t "Asociacion del problema" crlf)

    (assert(ent-asigs))
    (retract ?hecho)
)


(defrule escoge-horario-preferido
    (ent-asigs)
    (dni ?dni)
    ?prob-abs <- (problema-abstracto (horario-preferidoR $?td) (horario-preferidoP $?tdP))
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    ;(test (neq ?td nil))
    =>
    (printout t ">> Asociacion de Horario" crlf)
    
    ;Restricciones
    (if (= 1 (length$ ?td)) then
        (bind ?insh (find-instance ((?ins Horario)) (eq ?ins:horario (nth$ 1 ?td))))
        (bind ?ins-asigs (find-all-instances ((?ins Asignatura)) (not (interseccion-vacia ?insh ?ins:horarios))))

        (loop-for-count (?i 1 (length$ ?ins-asigs)) do
            (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo horario-preferido) (es-pref FALSE))) ;poner un motivo más user-friendly
        )
    )

    ;Preferencias
    (if (= 1 (length$ ?tdP)) then
        (bind ?resP (create$))
        (bind ?ins-asigsP (find-all-instances ((?ins Asignatura))
            (member ?tdP (create$ (progn$ (?cand (send ?ins get-horarios)) (insert$ ?resP (+ 1 (length$ ?resP)) (send ?cand get-horario)))))
        ))

        (loop-for-count (?i 1 (length$ ?ins-asigsP)) do
            (assert (nueva-rec (asign (nth$ ?i ?ins-asigsP)) (motivo horario-preferido) (es-pref TRUE))) ;poner un motivo más user-friendly
        )
    )
)

(defrule escoge-volumen-trabajo
    (ent-asigs)
    ?prob-abs <- (problema-abstracto (volumen-trabajoR ?vtR) (volumen-trabajoP ?vtP))
    ;(test (neq ?vt nil))
    =>
    (printout t ">> Asociacion de volumen de trabajo" crlf)
    
    (if (not(eq ?vtR nil))
        then
        (if (eq ?vtR bajo)
            then
            (bind ?minR 0)
            (bind ?maxR 20)
            else (if (eq ?vtR medio)
                then
                (bind ?minR 20)
                (bind ?maxR 40)
                else
                (bind ?minR 40)
                (bind ?maxR 50)
            )
        )
        (bind ?ins-asigs (find-all-instances ((?ins Asignatura))
            (and
                (<= ?minR (+ (send ?ins get-horas_lab) (send ?ins get-horas_prob)))
                (<= (+ (send ?ins get-horas_lab) (send ?ins get-horas_prob)) ?maxR))))

        (loop-for-count (?i 1 (length$ ?ins-asigs)) do
            (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo volumen-trabajo) (es-pref FALSE))) ;poner un motivo más user-friendly
        )
    )
    
    (if (not(eq ?vtP nil))
        then
        (if (eq ?vtP bajo)
            then
            (bind ?minP 0)
            (bind ?maxP 20)
            else (if (eq ?vtP medio)
                then
                (bind ?minP 20)
                (bind ?maxP 40)
                else
                (bind ?minP 40)
                (bind ?maxP 50)
            )
        )
        (bind ?ins-asigs (find-all-instances ((?ins Asignatura))
            (and
                (<= ?minP (+ (send ?ins get-horas_lab) (send ?ins get-horas_prob)))
                (<= (+ (send ?ins get-horas_lab) (send ?ins get-horas_prob)) ?maxP))))

        (loop-for-count (?i 1 (length$ ?ins-asigs)) do
            (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo volumen-trabajo) (es-pref TRUE))) ;poner un motivo más user-friendly
        )
    )
)

(defrule escoge-interes-compl-esp
    (ent-asigs)
    (dni ?dni)
    ?prob-abs <- (problema-abstracto (especialidadR ?espR) (especialidadP ?espP))
    ?al <- (object (is-a Alumno) (id ?dni) (especialidad ?e))
    ;(test (neq ?espR nil))
    =>
    (printout t ">> Asociacion de Especialidad" crlf)
    
    (if (not(eq ?espR nil))
        then
        (bind ?asigsR (find-all-instances ((?ins Especializada)) (member ?espR ?ins:especialidad_asig)))

        (loop-for-count (?i 1 (length$ ?asigsR)) do
            (assert (nueva-rec (asign (nth$ ?i ?asigsR)) (motivo interes-compl-esp) (es-pref FALSE))) ;poner un motivo más user-friendly
        )
    )
    
    (if (not(eq ?espP nil))
        then
        (bind ?asigsP (find-all-instances ((?ins Especializada)) (member ?espP ?ins:especialidad_asig)))

        (loop-for-count (?i 1 (length$ ?asigsP)) do
            (assert (nueva-rec (asign (nth$ ?i ?asigsP)) (motivo interes-compl-esp) (es-pref TRUE))) ;poner un motivo más user-friendly
        )
    )
)

(defrule escoge-intereses-tematicos
    (ent-asigs)
    ?prob-abs <- (problema-abstracto (intereses-tematicosR $?itR) (intereses-tematicosP $?itP))
    ;(test (!= 0 (length$ ?it)))
    =>
    (printout t ">> Asociacion de Tema" crlf)
    
    (if (!= 0 (length$ ?itR))
        then
        (bind ?ins-asigs (find-all-instances ((?ins Asignatura)) (not (interseccion-vacia ?itR ?ins:temas))))

        (loop-for-count (?i 1 (length$ ?ins-asigs)) do
            (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo intereses-tematicos) (es-pref FALSE))) ;poner un motivo más user-friendly
        )
    )
    
    (if (!= 0 (length$ ?itP))
        then
        (bind ?ins-asigs (find-all-instances ((?ins Asignatura)) (not (interseccion-vacia ?itP ?ins:temas))))

        (loop-for-count (?i 1 (length$ ?ins-asigs)) do
            (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo intereses-tematicos) (es-pref FALSE))) ;poner un motivo más user-friendly
        )
    )
)

(defrule escoge-intereses-competencias
    (ent-asigs)
    (dni ?dni)
    ?prob-abs <- (problema-abstracto (competenciasR $?comRes) (competenciasP $?comPref))
    ?al <- (object (is-a Alumno) (id ?dni) (especialidad ?e))
    ;(test (!= 0 (length$ ?comRes)))

    =>
    (printout t ">> Asociacion de Competencias" crlf)

    (bind ?ins-asigs-pref (find-all-instances ((?ins Asignatura)) (not (interseccion-vacia ?comPref ?ins:competencias))))
    (bind ?ins-asigs-rest (find-all-instances ((?ins Asignatura)) (not (interseccion-vacia ?comRes ?ins:competencias))))

    (loop-for-count (?i 1 (length$ ?ins-asigs-pref)) do
        (assert (nueva-rec (asign (nth$ ?i ?ins-asigs-pref)) (motivo intereses-competencias) (es-pref TRUE))) ;poner un motivo más user-friendly
    )
    (loop-for-count (?i 1 (length$ ?ins-asigs-rest)) do
        (assert (nueva-rec (asign (nth$ ?i ?ins-asigs-rest)) (motivo intereses-competencias) (es-pref FALSE))) ;poner un motivo más user-friendly
    )
)

(defrule escoge-curso
    (ent-asigs)
    ?prob-abs <- (problema-abstracto (curso-estudios ?ce))
    =>
    (printout t ">> Asociacion de Curso" crlf)
    
    (bind ?ins-asigs (find-all-instances ((?ins Asignatura)) (= (curso-a-int ?ins:curso) ?ce)))

    (loop-for-count (?i 1 (length$ ?ins-asigs)) do
        (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo sigue-plan-estudios) (es-pref TRUE))) ;poner un motivo más user-friendly
    )

    ;intentamos recomendar asignaturas del siguiente curso (por si el alumno está a punto de empezar uno nuevo)
    (if (< ?ce 4)
        then
        (bind ?ins-asigs2 (find-all-instances ((?ins Asignatura)) (= (curso-a-int ?ins:curso) (+ 1 ?ce))))
        (loop-for-count (?i 1 (length$ ?ins-asigs2)) do
            (assert (nueva-rec (asign (nth$ ?i ?ins-asigs2)) (motivo sigue-plan-estudios) (es-pref TRUE)))
        )
    )

)

(defrule escoge-especialidad-principal "Escoge asignaturas de la especialidad principal"
    (ent-asigs)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni) (especialidad ?e))
    (test (neq ?e [nil]))
    =>
    (printout t ">> Asociacion de Especialidad Principal" crlf)
    
    (bind ?ins-asigs (find-all-instances ((?ins Especializada)) (member ?e ?ins:especialidad_asig)))

    (loop-for-count (?i 1 (length$ ?ins-asigs)) do
        (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo sigue-esp-principal) (es-pref TRUE))) ;poner un motivo más user-friendly
    )
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
    (declare (salience 5))
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





(defrule fin-asociacion "Comprueba que se ejecuten todas las reglas de Asociacion"
    ?hecho1 <- (ent-asigs)
    =>
    (printout t "Fin asociacion" crlf)
    (assert(asociacion ok))
    (retract ?hecho1)
)
