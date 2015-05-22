;;
;; Estructuras para la asociacion heuristica de un problema abstracto a una solucion abstracta
;;

(defmodule asociacion "Módulo para la asociacion heuristica de un problema abstracto a una solucion abstracta"
    (import MAIN ?ALL)
    (import consultas deftemplate dni)
    (import respref deffunction curso-a-int)
    (import abstraccion deftemplate problema-abstracto)
    (export ?ALL)
)


(deftemplate asig-rec "Asignatura recomendada con sus motivos (a partir de todas las reglas)"
    (slot asign)
    (multislot motivosR (default (create$)))
    (multislot motivosP (default (create$)))
    (slot rest-sat) ;número de restricciones que satisface
    (slot pref-sat) ;número de preferencias que satisface
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
    (declare (salience 10))
    =>
    (assert(ent-asigs))
)

(deffunction horario-preferido
    (?es_pref $?td)
    
    (if (!= 0 (length$ ?td))
        then
        (bind ?horasI (create$))
        (loop-for-count (?i 1 (length$ td)) do
            (bind ?horaN (nth$ ?i ?td))
            (bind ?horaI (nth$ 1 (find-instance ((?ins Horario)) (eq ?ins:horario ?horaN))))
            (bind ?horasI (insert$ ?horasI 1 ?horaI))
        )
        
        (bind ?ins-asigs (find-all-instances ((?ins Asignatura)) (not (interseccion-vacia ?horasI ?ins:horarios))))
        
        (loop-for-count (?i 1 (length$ ?ins-asigs)) do
            (bind ?asig (nth$ ?i ?ins-asigs))
            (loop-for-count (?j 1 (length$ ?horasI)) do
                (bind ?hI (nth$ ?j ?horasI))
                (if (member ?hI (send ?asig get-horarios)) then
                    (bind ?motivo (str-cat "horario preferido-" (send ?hI get-horario)))
                    (assert (nueva-rec (asign ?asig) (motivo ?motivo) (es-pref ?es_pref))) ;poner un motivo más user-friendly
                )
            )
        )
    )
)

(defrule escoge-horario-preferido
    (ent-asigs)
    ?prob-abs <- (problema-abstracto (horario-preferidoR $?tdR) (horario-preferidoP $?tdP))
    =>
    (horario-preferido FALSE ?tdR)
    (horario-preferido TRUE ?tdP)
)

(deffunction tiempo-dedicacion
    (?td ?es_pref)
    
    (if (neq ?td nil) then
        (if (eq ?td "alto")
            then (bind ?max 100)
            else (if (eq ?td "medio") then (bind ?max 60)
            else (bind ?max 33)
        ))

        (bind ?ins-asigs (find-all-instances ((?ins Asignatura)) (<= (+ (send ?ins get-horas_teoria) (send ?ins get-horas_lab) (send ?ins get-horas_prob)) ?max)))
        (loop-for-count (?i 1 (length$ ?ins-asigs)) do
            (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo tiempo-dedicacion) (es-pref ?es_pref))) ;poner un motivo más user-friendly
        )
    )
)

(defrule escoge-tiempo-dedicacion
    (ent-asigs)
    ?prob-abs <- (problema-abstracto (tiempo-dedicacionR ?tdR) (tiempo-dedicacionP ?tdP))
    =>
    
    ;(tiempo-dedicacion ?tdR FALSE)
    ;(tiempo-dedicacion ?tdP TRUE)
)

(deffunction completar-esp
    (?esp ?es_pref)
    
    (if (not(eq ?esp nil))
        then
        (bind ?asigs (find-all-instances ((?ins Especializada)) (member ?esp ?ins:especialidad_asig)))

        (loop-for-count (?i 1 (length$ ?asigs)) do
            (bind ?motivo (str-cat "completar especialidad-" (send ?esp get-nombre_esp)))
            (assert (nueva-rec (asign (nth$ ?i ?asigs)) (motivo ?motivo) (es-pref ?es_pref))) ;poner un motivo más user-friendly
        )
    )
)

(defrule escoge-interes-compl-esp
    (ent-asigs)
    ?prob-abs <- (problema-abstracto (especialidadR ?espR) (especialidadP ?espP))
    =>
    (completar-esp ?espR FALSE)
    (completar-esp ?espP TRUE)
)

(deffunction intereses-tematicos
    (?es_pref $?it)
    
    (if (!= 0 (length$ ?it))
        then
        (bind ?ins-asigs (find-all-instances ((?ins Asignatura)) (not (interseccion-vacia ?it ?ins:temas))))
        
        (loop-for-count (?i 1 (length$ ?ins-asigs)) do
            (bind ?asig (nth$ ?i ?ins-asigs))
            (loop-for-count (?j 1 (length$ ?it)) do
                (bind ?tI (nth$ ?j ?it))
                (if (member ?tI (send ?asig get-temas)) then
                    (bind ?motivo (str-cat "intereses tematicos-" (send ?tI get-nombre_tema)))
                    (assert (nueva-rec (asign ?asig) (motivo ?motivo) (es-pref ?es_pref))) ;poner un motivo más user-friendly
                )
            )
        )
    )
)

(defrule escoge-intereses-tematicos
    (ent-asigs)
    ?prob-abs <- (problema-abstracto (intereses-tematicosR $?itR) (intereses-tematicosP $?itP))
    =>
    (intereses-tematicos FALSE ?itR)
    (intereses-tematicos TRUE ?itP)
)

(deffunction intereses-competencias
    (?es_pref $?com)
    
    (if (!= 0 (length$ ?com))
        then
        (bind ?ins-asigs (find-all-instances ((?ins Asignatura)) (not (interseccion-vacia ?com ?ins:competencias))))

        (loop-for-count (?i 1 (length$ ?ins-asigs)) do
            (bind ?asig (nth$ ?i ?ins-asigs))
            (loop-for-count (?j 1 (length$ ?com)) do
                (bind ?cI (nth$ ?j ?com))
                (if (member ?cI (send ?asig get-competencias)) then
                    (bind ?nombre (send ?cI get-nombre_comp))
                    (bind ?nivel (send ?cI get-nivel))
                    (bind ?motivo (str-cat (str-cat "intereses competencias-" ?nombre) (str-cat "-" ?nivel)))
                    (assert (nueva-rec (asign ?asig) (motivo ?motivo) (es-pref ?es_pref))) ;poner un motivo más user-friendly
                )
            )
        )
    )
)

(defrule escoge-intereses-competencias
    (ent-asigs)
    ?prob-abs <- (problema-abstracto (competenciasR $?comRes) (competenciasP $?comPref))

    =>
    (intereses-competencias FALSE ?comRes)
    (intereses-competencias TRUE ?comPref)
)

(deffunction dificultad
    (?dif ?es_pref)
    
    (if (not(eq ?dif nil))
        then
        (bind $?asigs-dificiles (find-all-instances ((?ins Asignatura)) (< ?ins:aprobados_ant 70)))
        (bind $?asigs-faciles (find-all-instances ((?ins Asignatura)) (not(member ?ins ?asigs-dificiles))))

        (loop-for-count (?i 1 (length$ ?asigs-faciles)) do
            (assert (nueva-rec (asign (nth$ ?i ?asigs-faciles)) (motivo "dificultad-Facil") (es-pref ?es_pref))) ;poner un motivo más user-friendly
        )
        
        (if (eq ?dif dificil)
            then
            (loop-for-count (?i 1 (length$ ?asigs-dificiles)) do
                (assert (nueva-rec (asign (nth$ ?i ?asigs-dificiles)) (motivo "dificultad-Dificil") (es-pref ?es_pref))) ;poner un motivo más user-friendly
            )
        )
    )
)

(defrule escoge-dificultad
    (ent-asigs)
    ?prob-abs <- (problema-abstracto (dificultadR ?difRes) (dificultadP ?difPref))
    
    =>
    (dificultad ?difRes FALSE)
    (dificultad ?difPref TRUE)
)



(defrule escoge-curso
    (ent-asigs)
    ?prob-abs <- (problema-abstracto (curso-estudios ?ce))
    =>
    (bind ?ins-asigs (find-all-instances ((?ins Asignatura)) (= (curso-a-int ?ins:curso) ?ce)))

    (loop-for-count (?i 1 (length$ ?ins-asigs)) do
        (bind ?motivo (str-cat "sigue plan estudios-" ?ce))
        (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo ?motivo) (es-pref TRUE)))
        (bind ?motivo (str-cat "sigue curso actual-" ?ce)) ;motivo adicional para dar prioridad a que acabe el curso actual (útil para que no aparezca EEE en fase inicial, p.e.)
        (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo ?motivo) (es-pref TRUE)))
    )

    ;intentamos recomendar asignaturas del siguiente curso (por si el alumno está a punto de empezar uno nuevo)
    (if (< ?ce 4)
        then
        (bind ?ins-asigs2 (find-all-instances ((?ins Asignatura)) (= (curso-a-int ?ins:curso) (+ 1 ?ce))))
        (loop-for-count (?i 1 (length$ ?ins-asigs2)) do
            (bind ?motivo (str-cat "sigue plan estudios-" (+ 1 ?ce)))
            (assert (nueva-rec (asign (nth$ ?i ?ins-asigs2)) (motivo ?motivo) (es-pref TRUE)))
        )
    )

)

(defrule escoge-especialidad-principal "Escoge asignaturas de la especialidad principal"
    (ent-asigs)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni) (especialidad ?e))
    (test (neq ?e [nil]))
    =>
    (bind ?ins-asigs (find-all-instances ((?ins Especializada)) (member ?e ?ins:especialidad_asig)))

    (loop-for-count (?i 1 (length$ ?ins-asigs)) do
        (assert (nueva-rec (asign (nth$ ?i ?ins-asigs)) (motivo sigue-esp-principal) (es-pref TRUE))) ;poner un motivo más user-friendly
    )
)


(deffunction ha-aprobado "Retorna si el alumno ?al ha aprobado la asignatura ?a"
    (?al ?a)

    (bind ?nombre-cand (send ?a get-nombre))
    (bind ?notas (send (send ?al get-expediente_alumno) get-notas_exp))
    (progn$ (?ins ?notas)
        (if (and (eq ?nombre-cand (send (send (send ?ins get-convocatoria_nota) get-asignatura_conv) get-nombre)) (>= (send ?ins get-nota) 5))
            then
            (return TRUE)
        )
    )
    (return FALSE)
)


(defrule escoge-suspendidas "Escoge asignaturas suspendidas"
    (ent-asigs)
    (dni ?dni)
    ?al <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    =>
    (bind $?notas (send ?exped get-notas_exp))
    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?nota (send ?not get-nota))
        (if (< ?nota 5)
            then
            (bind ?conv (send ?not get-convocatoria_nota))
            (bind ?asig (send ?conv get-asignatura_conv))
            (if (not (ha-aprobado ?al ?asig))
                then
                (assert (nueva-rec (asign ?asig) (motivo asignatura-suspensa) (es-pref TRUE))) ;poner un motivo más user-friendly
            )
        )
    )
)



(defrule modifica-asig-rec "Modifica una asignatura recomendada (añade motivo y/o pref-sat)"
    (declare (salience 10)) ;tiene prioridad para comprobar si ya existe la asig-rec
    ?nr <- (nueva-rec (asign ?a) (motivo ?m) (es-pref ?ep))
    ?ar <- (asig-rec (asign ?a) (motivosR $?msR) (motivosP $?msP) (rest-sat ?rs) (pref-sat ?ps))
    =>
    (if (eq ?ep TRUE)
        then
        (bind ?ps-nuevo (+ 1 ?ps))
        (bind ?rs-nuevo ?rs)
        (bind ?ar (modify ?ar (motivosP (insert$ ?msP 1 ?m)) (rest-sat ?rs-nuevo) (pref-sat ?ps-nuevo)))
        else
        (bind ?ps-nuevo ?ps)
        (bind ?rs-nuevo (+ 1 ?rs))
        (bind ?ar (modify ?ar (motivosR (insert$ ?msR 1 ?m)) (rest-sat ?rs-nuevo) (pref-sat ?ps-nuevo)))
    )
    

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
        (assert (asig-rec (asign ?a) (motivosP (create$ ?m)) (rest-sat ?rs) (pref-sat ?ps)))
        else
        (bind ?ps 0)
        (bind ?rs 1)
        (assert (asig-rec (asign ?a) (motivosR (create$ ?m)) (rest-sat ?rs) (pref-sat ?ps)))
    )

    (retract ?nr)
)



(defrule fin-asociacion "Comprueba que se ejecuten todas las reglas de Asociacion"
    ?hecho1 <- (ent-asigs)
    =>
    (retract ?hecho1)

    (focus refinamiento)
)