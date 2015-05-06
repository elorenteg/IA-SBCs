;;
;; Estructuras para la asociacion heuristica de un problema abstracto a una solucion abstracta
;;

(defrule entrada-asociacion "Asociacion heuristica del problema"
    ?hecho <- (abstraccion ok)
    =>
    ;;; TODO: abstraccion del problema ;;;
    (printout t "Asociacion del problema" crlf)
    
    (retract ?hecho)
)
