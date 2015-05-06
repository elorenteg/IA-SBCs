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
    (slot horario-preferidoR (allowed-strings "manyana" "tarde"))
    (slot horario-preferidoP (allowed-strings "manyana" "tarde"))
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
    
    (retract ?hecho)
)

(defrule abs-horario "Abstrae restricciones y preferencias sobre el horario"
    ?hecho <- (ent-abs-horario)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (name ?na) (id ?dni))
    ?res <- (respref (es_restriccion TRUE) (tipo_horario $?tipo-horarioR))
    ?pref <- (respref (es_restriccion FALSE) (tipo_horario $?tipo-horarioP))
    ;(object (is-a Tipo_Horario) (name ?nrp) (es_preferencia ?es-pref) (tipo_horario ?th))
    ;(test (>= 1 (member-wrapper ?nrp (send ?na get-respref_alumno))))

    =>

    (printout t "Abstraccion de Horario" crlf)
    
    
    (assert(abs-horario ok))
    (retract ?hecho)
)

(defrule fin-abstracto "Comprueba que se ejecuten todas las reglas de Abstraccion"
    ?hecho1 <- (abs-horario ok)
    =>
    (printout t "Fin abstraccion" crlf)
    (assert(abstraccion ok))
    (retract ?hecho1)
)