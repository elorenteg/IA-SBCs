;;
;; Estructuras para la abstracción de un problema concreto a uno más general
;;


(deftemplate problema-abstracto "Conjunto de características que definen un problema abstracto"
    (slot dificultad (allowed-strings "alta" "media"))
    (slot volumen-trabajo (allowed-strings "alto" "medio" "bajo"))
    (multislot intereses-tematicos (type INSTANCE))
    (slot especialidad (type INSTANCE))
    (slot interes-compl-esp (allowed-strings "alto" "medio" "ninguno"))
    (slot tiempo-dedicacion (allowed-strings "alto" "medio" "bajo"))
    (slot horario-preferido (allowed-strings "manyana" "tarde"))
)

;;; TODO: dar peso a las características de problema-abstacto, según sean restricciones o preferencias ;;;


(deffunction member-wrapper "Si X no es miembro de L, devuelve 0"
    (?X ?L)

    (bind ?res (member ?X ?L))
    (if (eq (type ?res) SYMBOL) then (return 0)) ;evito que devuelva FALSE
    ?res
)

(defrule abs-horario "Abstrae restricciones y preferencias sobre el horario"
    (prefs ok)
    (restrs ok)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (name ?na) (id ?dni))
    (object (is-a Tipo_Horario) (name ?nrp) (es_preferencia ?es-pref) (tipo_horario ?th))
    (test (>= 1 (member-wrapper ?nrp (send ?na get-respref_alumno))))

    =>

    (printout t "Alumno " ?na " tiene Respref " ?nrp ". Es preferencia? " ?es-pref ". Tipo de horario: " ?th crlf)
    ;;; TODO: hacer algo con los datos de las resprefs del alumno ;;;
)

;(defrule abs-horario-inf "Infiere conocimiento sobre el horario")