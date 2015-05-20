;;
;; Estructuras para la abstracción de un problema concreto a uno más general
;;

(defmodule abstraccion "Módulo para la abstracción de un problema concreto a uno más general"
    (import MAIN ?ALL)
    (import consultas deftemplate dni)
    (import respref deftemplate respref)
    (import respref deftemplate curso)
    (export ?ALL)
)


(deftemplate problema-abstracto "Conjunto de características que definen un problema abstracto"
    (slot dificultadR (allowed-strings "alta" "media"))
    (slot dificultadP (allowed-strings "alta" "media"))
    (slot volumen-trabajoR (allowed-strings "alto" "medio" "bajo"))
    (slot volumen-trabajoP (allowed-strings "alto" "medio" "bajo"))
    (multislot intereses-tematicosR (type INSTANCE))
    (multislot intereses-tematicosP (type INSTANCE))
    (slot especialidadR (type INSTANCE))
    (slot especialidadP (type INSTANCE))
    (multislot competenciasR (type INSTANCE))
    (multislot competenciasP (type INSTANCE))
    (slot tiempo-dedicacionR (allowed-strings "alto" "medio" "bajo"))
    (slot tiempo-dedicacionP (allowed-strings "alto" "medio" "bajo"))
    (multislot horario-preferidoR (allowed-strings "manyana" "tarde") (default (create$)))
    (multislot horario-preferidoP (allowed-strings "manyana" "tarde") (default (create$)))
    (slot curso-estudios) ;curso del plan de estudios
)


(deffunction member-wrapper "Si X no es miembro de L, devuelve 0"
    (?X ?L)

    (bind ?res (member ?X ?L))
    (if (eq (type ?res) SYMBOL) then (return 0)) ;evito que devuelva FALSE
    ?res
)

(defrule entrada-abstracto "Abstrae el problema"
    (declare (salience 10))
    =>
    (printout t "Abstraccion del problema" crlf)

    (assert (ent-abs-horario) (ent-abs-especialidad) (ent-abs-dificultad) (ent-abs-tema) (ent-abs-competencias) (ent-abs-curso))
    (assert (problema-abstracto))
)

(defrule abs-horario "Abstrae restricciones y preferencias sobre el horario"
    ?hecho <- (ent-abs-horario)
    (dni ?dni)
    ?res <- (respref (es_restriccion TRUE) (tipo_horario $?thRes))
    ?pref <- (respref (es_restriccion FALSE) (tipo_horario $?thPref))
    ?abs <- (problema-abstracto (horario-preferidoR $?absRes) (horario-preferidoP $?absPref))

    =>

    (printout t ">> Abstraccion de Horario" crlf)
    (if (> (length$ ?thRes) 0)
        then
        (loop-for-count (?i 1 (length$ ?thRes)) do
            (bind ?hora (nth$ ?i ?thRes))
            (bind ?absRes (insert$ ?absRes 1 (send ?hora get-horario)))
            (bind ?abs (modify ?abs (horario-preferidoR ?absRes)))
        )
    )
    (if (= (length$ ?thPref) 1)
        then
        (loop-for-count (?i 1 (length$ ?thPref)) do
            (bind ?hora (nth$ ?i ?thPref))
            (bind ?absPref (insert$ ?absPref 1 (send ?hora get-horario)))
            (bind ?abs (modify ?abs (horario-preferidoP ?absPref)))
        )
    )

    (assert(abs-horario ok))
    (retract ?hecho)
)

(defrule abs-dificultad
    ?hecho <- (ent-abs-dificultad)
    (dni ?dni)
    ?res <- (respref (es_restriccion TRUE) (dificultad ?difRes))
    ?pref <- (respref (es_restriccion FALSE) (dificultad ?difPref))
    ?abs <- (problema-abstracto (dificultadR ?absRes) (dificultadP ?absPref))

    =>

    (printout t ">> Abstraccion de Dificultad" crlf)

    (bind ?abs (modify ?abs (dificultadR nil)))
    (if (eq (str-compare ?difPref "Facil") 0)
        then
        (bind ?abs (modify ?abs (dificultadP "media")))
        else
        (bind ?abs (modify ?abs (dificultadP "alta")))
    )

    (assert(abs-dificultad ok))
    (retract ?hecho)
)

(defrule abs-tema
    ?hecho <- (ent-abs-tema)
    (dni ?dni)
    ?res <- (respref (es_restriccion TRUE) (tema_especializado $?temRes))
    ?pref <- (respref (es_restriccion FALSE) (tema_especializado $?temPref))
    ?abs <- (problema-abstracto (intereses-tematicosR $?absRes) (intereses-tematicosP $?absPref))

    =>

    (printout t ">> Abstraccion de Interes Tematico" crlf)

    (bind ?abs (modify ?abs (intereses-tematicosR ?temRes)))
    (bind ?abs (modify ?abs (intereses-tematicosP ?temPref)))

    (assert(abs-tema ok))
    (retract ?hecho)
)

(defrule abs-especialidad
    ?hecho <- (ent-abs-especialidad)
    (dni ?dni)
    ?res <- (respref (es_restriccion TRUE) (completar_especialidad ?espRes))
    ?pref <- (respref (es_restriccion FALSE) (completar_especialidad ?espPref))
    ?abs <- (problema-abstracto (especialidadR ?espR) (especialidadP ?espP))

    =>

    (printout t ">> Abstraccion de Especialidad" crlf)
    (bind ?abs (modify ?abs (especialidadR ?espRes)))
    (bind ?abs (modify ?abs (especialidadP ?espPref)))

    (assert(abs-especialidad ok))
    (retract ?hecho)
)

(deffunction compet-a-superar
    (?exped $?compet)

    (bind $?notas (send ?exped get-notas_exp))
    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?conv (send ?not get-convocatoria_nota))
        (bind ?asig (send ?conv get-asignatura_conv))
        (bind $?com (send ?asig get-competencias))
        (bind ?nota (send ?not get-nota))

        ; borramos las competencias de nivel inferior y del mismo nivel (si la tiene superada)
        (bind $?indices (create$))
        (loop-for-count (?j 1 (length$ ?compet)) do
            (bind ?compI (nth$ ?j ?compet))
            (bind ?nomC (send ?compI get-nombre_comp))
            (bind ?nivC (send ?compI get-nivel))

            (loop-for-count (?k 1 (length$ ?com)) do
                (bind ?inst (nth$ ?k ?com))
                (bind ?nom (send ?inst get-nombre_comp))
                (bind ?niv (send ?inst get-nivel))
                (if (eq (str-compare ?nom ?nomC) 0)
                    then
                    (if (eq (str-compare ?niv ?nivC) 1) ; la comp de la asig es de nivel superior a la posible recomendada
                        then
                        (if (not(member ?j ?indices)) then (bind $?indices (insert$ ?indices 1 ?j)))
                        else
                        (if (and (eq (str-compare ?niv ?nivC) 0) (not(< ?nota 5.0))) ; la comp de la asig es del mismo nivel y ya la ha superado
                            then
                           (if (not(member ?j ?indices)) then (bind $?indices (insert$ ?indices 1 ?j)))
                        )
                    )
                )
            )
        )

        (loop-for-count (?j 1 (length$ ?indices)) do
            (bind ?ind (nth$ ?j ?indices))
            (bind $?compet (delete$ ?compet ?ind ?ind))
        )
    )


    (return ?compet)
)

(defrule abs-competencias
    ?hecho <- (ent-abs-competencias)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    ?res <- (respref (es_restriccion TRUE) (competencias_preferidas $?comRes))
    ?pref <- (respref (es_restriccion FALSE) (competencias_preferidas $?comPref))
    ?abs <- (problema-abstracto (competenciasR $?absRes) (competenciasP $?absPref))

    =>

    (printout t ">> Abstraccion de Competencias" crlf)
    (bind $?compet $?comPref)

    ;;; reduccion de las competencias al nivel que le falta por cursar
    (bind $?competP (compet-a-superar ?exped ?comPref))
    (bind $?competR (compet-a-superar ?exped ?comRes))

    (bind ?abs (modify ?abs (competenciasR ?competR)))
    (bind ?abs (modify ?abs (competenciasP ?competP)))

    (assert(abs-competencias ok))
    (retract ?hecho)
)

(defrule abs-curso
    ?hecho <- (ent-abs-curso)
    ?hecho2 <- (curso ?max-curso)
    ?abs <- (problema-abstracto (curso-estudios ?ce))
    =>
    (printout t ">> Abstraccion de Curso" crlf)
    (bind ?abs (modify ?abs (curso-estudios ?max-curso)))

    (assert (abs-curso ok))
    (retract ?hecho)
)

(defrule fin-abstracto "Comprueba que se ejecuten todas las reglas de Abstraccion"
    ?hecho1 <- (abs-horario ok)
    ?hecho2 <- (abs-tema ok)
    ?hecho3 <- (abs-dificultad ok)
    ?hecho4 <- (abs-especialidad ok)
    ?hecho5 <- (abs-competencias ok)
    ?hecho6 <- (abs-curso ok)
    =>
    (printout t "Fin abstraccion" crlf)
    (retract ?hecho1 ?hecho2 ?hecho3 ?hecho4 ?hecho5 ?hecho6)

    (focus asociacion)
)