;;
;; Estructuras para la abstracción de un problema concreto a uno más general
;;

(deftemplate problema-abstracto "Conjunto de características que definen un problema abstracto"
    (slot dificultadR (allowed-strings "alta" "media"))
    (slot dificultadP (allowed-strings "alta" "media"))
    (slot volumen-trabajoR (allowed-strings "alto" "medio" "bajo"))
    (slot volumen-trabajoP (allowed-strings "alto" "medio" "bajo"))
    (multislot intereses-tematicosR (type INSTANCE))
    (multislot intereses-tematicosP (type INSTANCE))
    (slot especialidadR (type INSTANCE))
    (slot especialidadP (type INSTANCE))
    (slot interes-compl-espR (allowed-strings "alto" "medio" "ninguno"))
    (slot interes-compl-espP (allowed-strings "alto" "medio" "ninguno"))
    (slot tiempo-dedicacionR (allowed-strings "alto" "medio" "bajo"))
    (slot tiempo-dedicacionP (allowed-strings "alto" "medio" "bajo"))
    (multislot horario-preferidoR (allowed-strings "manyana" "tarde") (default (create$)))
    (multislot horario-preferidoP (allowed-strings "manyana" "tarde") (default (create$)))
)

;;; TODO: dar peso a las características de problema-abstacto, según sean restricciones o preferencias ;;;

(deffunction member-wrapper "Si X no es miembro de L, devuelve 0"
    (?X ?L)

    (bind ?res (member ?X ?L))
    (if (eq (type ?res) SYMBOL) then (return 0)) ;evito que devuelva FALSE
    ?res
)

(defrule entrada-abstracto "Abstrae el problema"
    ?hecho <- (inferencia ok)
    =>
    ;;; TODO: abstraccion del problema ;;;
    (printout t "Abstraccion del problema" crlf)
    
    (assert(ent-abs-horario))
    (assert (problema-abstracto))
    (retract ?hecho)
)

(defrule abs-horario "Abstrae restricciones y preferencias sobre el horario"
    ?hecho <- (ent-abs-horario)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (name ?na) (id ?dni))
    ?res <- (respref (es_restriccion TRUE) (tipo_horario $?thRes))
    ?pref <- (respref (es_restriccion FALSE) (tipo_horario $?thPref))
    ?abs <- (problema-abstracto (horario-preferidoR $?absRes) (horario-preferidoP $?absPref))
    
    ;(object (is-a Tipo_Horario) (name ?nrp) (es_preferencia ?es-pref) (tipo_horario ?th))
    ;(test (>= 1 (member-wrapper ?nrp (send ?na get-respref_alumno))))

    =>

    (printout t ">> Abstraccion de Horario" crlf)
    (if (= (length$ ?thRes) 1)
        then
        (bind ?hora (nth$ 1 ?thRes)) ; instancia Tipo_Horario
        (bind ?absRes (send ?hora get-horario)) ; valor del horario
        (bind ?abs (modify ?abs (horario-preferidoR ?absRes))) ; añadir a la abstraccion
        else
        (bind ?absRes (insert$ ?absRes 1 "Manyana"))
        (bind ?absRes (insert$ ?absRes 2 "Tarde"))
        (bind ?abs (modify ?abs (horario-preferidoR ?absRes)))
    )
    (if (= (length$ ?thPref) 1)
        then
        (bind ?hora (nth$ 1 ?thPref)) ; instancia Tipo_Horario
        (bind ?absPref (send ?hora get-horario)) ; valor del horario
        (bind ?abs (modify ?abs (horario-preferidoP ?absPref))) ; añadir a la abstraccion
        else
        (bind ?absPref (insert$ ?absPref 1 "Manyana"))
        (bind ?absPref (insert$ ?absPref 2 "Tarde"))
        (bind ?abs (modify ?abs (horario-preferidoP ?absPref)))
    )
    
    (assert(abs-horario ok))
    (retract ?hecho)
)

;;; TODO: una regla por cada abstraccion a realizar o una sola regla para todo ;;;

(defrule fin-abstracto "Comprueba que se ejecuten todas las reglas de Abstraccion"
    ?hecho1 <- (abs-horario ok)
    =>
    (printout t "Fin abstraccion" crlf)
    (assert(abstraccion ok))
    (retract ?hecho1)
)