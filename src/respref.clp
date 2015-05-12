;;
;; Estructuras para la recogida de datos de restricciones/preferencias
;;

(deftemplate respref
    (slot es_restriccion)
    (multislot competencias_preferidas)
    (multislot completar_especialidad)
    (slot dificultad)
    (slot max_asigns)
    (slot max_horas_trabajo)
    (slot max_horas_lab)
    (multislot tema_especializado)
    (multislot tipo_horario)
)

(deffunction sort-list
    ($?list)
    
    (bind $?sin-repes (create$))
    (loop-for-count (?i 1 (length$ ?list)) do
        (bind ?elem (nth$ ?i ?list))
        (if (not(member$ ?elem ?sin-repes))
            then
            (bind ?sin-repes (insert$ ?sin-repes 1 ?elem))
        )
    )
    
    (loop-for-count (?i 1 (length$ ?sin-repes)) do
        (bind ?min ?i)
        (loop-for-count (?j (+ ?i 1) (length$ ?sin-repes)) do
            (if (< (str-compare (nth$ ?j ?sin-repes) (nth$ ?min ?sin-repes)) 0)
                then
                (bind ?min ?j)
            )
        )
        (if (!= ?min ?i)
            then
            (bind ?auxI (nth$ ?i ?sin-repes))
            (bind ?auxM (nth$ ?min ?sin-repes))
            (bind ?sin-repes (replace$ ?sin-repes ?i ?i ?auxM))
            (bind ?sin-repes (replace$ ?sin-repes ?min ?min ?auxI))
        )
    )
    
    ?sin-repes
)

(deffunction find-index
    (?elem $?list)
    
    (loop-for-count (?i 1 (length$ ?list)) do
        (bind ?e (nth$ ?i ?list))
        (if (eq ?elem ?e)
            then
            (return ?i)
        )
    )
    
    (return 0)
)


(defrule entrada-respref "Pide las preferencias y las restricciones"
    (dni ?dni)
    =>
    (printout t "Entrada de restricciones/preferencias" crlf)
	(assert (ent-respref FALSE))
    (assert (ent-respref TRUE))
    (assert (respref (es_restriccion TRUE)))
    (assert (respref (es_restriccion FALSE)))
)

(defrule preguntas-respref "Modifica los hechos de ResPref segun lo que pida el alumno"
    ?hecho <- (ent-respref ?es-rest)
	(dni ?dni)
	?alumn <- (object (is-a Alumno) (id ?dni))  ; ?alumn es la instancia del alumno con id ?dni al que le queremos introducir las respref
    ?rec <- (respref (es_restriccion ?es-rest))

	=>

	(if (eq ?es-rest TRUE)
		then
		(progn (format t ">> Restricciones%n") (assert (restrs ok)))
		else
		(progn (format t ">> Preferencias%n") (assert (prefs ok)))
	)

    
    (retract ?hecho)
)

(defrule contador-restricciones
    ?hecho1 <- (prefs ok)
    ?hecho2 <- (restrs ok)
    ?rest <- (respref (es_restriccion TRUE) (competencias_preferidas $?cp) (completar_especialidad $?ce) (dificultad ?d) 
                    (max_asigns ?ma) (max_horas_trabajo ?mht) (max_horas_lab ?mhl) (tema_especializado $?te) (tipo_horario $?th))
                    
    =>
    
    (printout t "Contador de restricciones" crlf)
    (bind ?nrest 0)
    (if (> (length$ ?cp) 0) then (bind ?nrest (+ ?nrest 1)))
    (if (> (length$ ?ce) 0) then (bind ?nrest (+ ?nrest 1)))
    (if (neq ?d nil) then (bind ?nrest (+ ?nrest 1)))
    (if (neq ?ma nil) then (bind ?nrest (+ ?nrest 1)))
    (if (neq ?mht nil) then (bind ?nrest (+ ?nrest 1)))
    (if (neq ?mhl nil) then (bind ?nrest (+ ?nrest 1)))
    (if (> (length$ ?te) 0) then (bind ?nrest (+ ?nrest 1)))
    (if (> (length$ ?th) 0) then (bind ?nrest (+ ?nrest 1)))
    
    (printout t ">> num. restricciones: " ?nrest crlf)
    
    (assert (contador ok))
    (assert (nrestricciones ?nrest))
    (retract ?hecho1)
    (retract ?hecho2)
)

(defrule inferencia-preferencias "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (contador ok)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    ?pref <- (respref (es_restriccion FALSE) (competencias_preferidas $?cp) (completar_especialidad $?ce) (dificultad ?d) 
                    (max_asigns ?ma) (max_horas_trabajo ?mht) (max_horas_lab ?mhl) (tema_especializado $?te) (tipo_horario $?th))
    
    =>
    
    ;;; TODO: inferencia de respref ;;;
    (printout t "Inferencia de preferencias" crlf)

    (bind $?notas (send ?exped get-notas_exp))
    
    (bind ?nasig 0) ; numero de asignaturas cursadas
    (bind ?ncred 0) ; numero de creditos cursados
    (bind ?nhoras-teo 0) ; numero de horas de teoria cursadas
    (bind ?nhoras-lab 0) ; numero de horas de lab cursadas
    (bind ?nhoras-pro 0) ; numero de horas de problemas cursadas
    (bind $?cuatris (create$)) ; cuatris en los que ha cursado alguna asignatura
    (bind $?nasigCu (create$)) ; numero de asignaturas por cada cuatri cursado (mismas posiciones que $?cuatris)
    (bind $?temas (create$)) ; temas de las asignaturas cursadas
    
    (bind $?asigns (create$))
    (bind $?repets (create$))
    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?conv (send ?not get-convocatoria_nota))
        (bind ?asig (send ?conv get-asignatura_conv))
        (bind ?cuat (send ?conv get-cuatrimestre))
        (bind $?tem (send ?asig get-temas))
        (bind ?cred (send ?asig get-num_creditos))
        (bind ?horT (send ?asig get-horas_teoria))
        (bind ?horL (send ?asig get-horas_lab))
        (bind ?horP (send ?asig get-horas_lab))
        
        (bind ?nasig (+ ?nasig 1))
        (bind ?ncred (+ ?nasig ?cred))
        (bind ?nhoras-teo (+ ?nhoras-teo ?horT))
        (bind ?nhoras-lab (+ ?nhoras-lab ?horL))
        (bind ?nhoras-pro (+ ?nhoras-pro ?horP))
        
        (if (not (member ?cuat ?cuatris))
            then
            (bind ?cuatris (insert$ ?cuatris 1 ?cuat))
            (bind ?nasigCu (insert$ ?nasigCu 1 1))
            else
            (bind ?ind (find-index ?cuat ?cuatris))
            (bind ?nasigCu (replace$ ?nasigCu ?ind ?ind (+(nth$ ?ind ?nasigCu)1)))
        )
        
        
        (loop-for-count (?j 1 (length$ ?tem)) do
            (bind ?tem-j (nth$ ?j ?tem))
            (if (not (member ?tem-j ?temas))
                then
                (bind ?temas (insert$ ?temas 1 ?tem-j))
            )
        )
        
        
        (if (not (member ?asig ?asigns))
            then
            (bind ?asigns (insert$ ?asigns 1 ?asig))
            else
            (bind ?repets (insert$ ?repets 1 ?asig))
        )
    )
    
    (if (= (length$ ?cp) 0) then (printout t "cp" crlf))
    (if (= (length$ ?ce) 0) then (printout t "ce" crlf))
    (if (eq ?d nil) then (printout t "d" crlf))
    (if (eq ?ma nil)
        then
        (bind ?mediaAs (div ?nasig (length$ ?cuatris)))
        (printout t "ma " ?mediaAs crlf)
        (bind ?pref (modify ?pref (max_asigns ?mediaAs)))
    )
    (if (eq ?mht nil)
        then
        (bind ?mediaHT (div ?nhoras-teo (length$ ?cuatris)))
        (printout t "mht " ?mediaHT crlf)
        (bind ?pref (modify ?pref (max_horas_trabajo ?mediaHT)))
    )
    (if (eq ?mhl nil)
        then
        (bind ?mediaHL (div (+ ?nhoras-lab ?nhoras-pro) (length$ ?cuatris)))
        (printout t "mhl " ?mediaHL crlf)
        (bind ?pref (modify ?pref (max_horas_trabajo ?mediaHL)))
    )
    (if (= (length$ ?te) 0) then (printout t "te" crlf))
    (if (= (length$ ?th) 0) then (printout t "th" crlf))
    
    (assert(inferencia ok))
    (retract ?hecho)
)