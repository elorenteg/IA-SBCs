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
    (printout t "Abstraccion del problema" crlf)
    ;;; TODO: abstraccion del problema ;;;
    ;;; esta funcion solo genera los hechos para ejecutar las reglas de abstraccion ;;;

    (assert (ent-abs-dedicacion) (ent-abs-horario))
    (assert (problema-abstracto))
    (retract ?hecho)
)

(defrule abs-volumenDedicacion "Abstrae restricciones y preferencias sobre el volumen de dedicacion y el tiempo"
    ?hecho <- (ent-abs-dedicacion)
    ?res <- (respref (es_restriccion TRUE) (max_asigns ?asigsRes) (max_horas_trabajo ?horasRes) (max_horas_lab ?labRes))
    ?pref <- (respref (es_restriccion FALSE) (max_asigns ?asigsPref) (max_horas_trabajo ?horasPref) (max_horas_lab ?labPref))
    ?abs <- (problema-abstracto (volumen-trabajoR ?volRes) (volumen-trabajoP ?volPref) (tiempo-dedicacionR ?tPref) (tiempo-dedicacionP ?tPref))

    =>

    (printout t ">> Abstraccion del volumen de dedicacion y el tiempo" crlf)
    (if (not(eq ?asigsRes nil))
        then
        (if (<= ?asigsRes 2)
            then
            (bind ?abs (modify ?abs (volumen-trabajoR "bajo")))
            else
            (if (<= ?asigsRes 4)
                then
                (bind ?abs (modify ?abs (volumen-trabajoR "medio")))
                else
                (bind ?abs (modify ?abs (volumen-trabajoR "alto")))
            )
        )
    )
    (if (not(eq ?horasRes nil))
        then
        (if (<= ?horasRes 300)
            then
            (bind ?abs (modify ?abs (tiempo-dedicacionR "bajo")))
            else
            (if (<= ?horasRes 600)
                then
                (bind ?abs (modify ?abs (tiempo-dedicacionR "medio")))
                else
                (bind ?abs (modify ?abs (tiempo-dedicacionR "alto")))
            )
        )
    )
    (if (not(eq ?asigsPref nil))
        then
        (if (<= ?asigsPref 2)
            then
            (bind ?abs (modify ?abs (volumen-trabajoP "bajo")))
            else
            (if (<= ?asigsPref 4)
                then
                (bind ?abs (modify ?abs (volumen-trabajoP "medio")))
                else
                (bind ?abs (modify ?abs (volumen-trabajoP "alto")))
            )
        )
    )
    (if (not(eq ?horasPref nil))
        then
        (if (<= ?horasPref 300)
            then
            (bind ?abs (modify ?abs (tiempo-dedicacionP "bajo")))
            else
            (if (<= ?horasPref 600)
                then
                (bind ?abs (modify ?abs (tiempo-dedicacionP "medio")))
                else
                (bind ?abs (modify ?abs (tiempo-dedicacionP "alto")))
            )
        )
    )
    (assert(abs-dedicacion ok))
    (retract ?hecho)
)

(defrule abs-horario "Abstrae restricciones y preferencias sobre el horario"
    ?hecho <- (ent-abs-horario)
    (dni ?dni)
    ?res <- (respref (es_restriccion TRUE) (tipo_horario $?thRes))
    ?pref <- (respref (es_restriccion FALSE) (tipo_horario $?thPref))
    ?abs <- (problema-abstracto (horario-preferidoR $?absRes) (horario-preferidoP $?absPref))

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
    ?hecho1 <- (abs-dedicacion ok)
    ?hecho2 <- (abs-horario ok)
    =>
    ;;; esta regla elimina los hechos usados en la abstraccion y genera un assert conforme ha acabado ;;;
    (printout t "Fin abstraccion" crlf)
    (assert(abstraccion ok))
    (retract ?hecho1 ?hecho2)
)