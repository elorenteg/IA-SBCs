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

    
    (bind ?ma (pregunta-rango ">> Cual es el numero maximo de asignaturas a matricular?" TRUE 1 6))
    (if (not(eq ?ma nil))
        then
        (bind ?rec (modify ?rec (max_asigns ?ma)))
    )

    (bind ?mh (pregunta-rango ">> Cual es el numero maximo de horas de dedicacion semanales?" TRUE 0 900))
    (if (not(eq ?mh nil))
        then
        (bind ?rec (modify ?rec (max_horas_trabajo ?mh)))
    )

    (bind ?ml (pregunta-rango ">> Cual es el numero maximo de horas de laboratorio semanales?" TRUE 0 900))
    (if (not(eq ?ml nil))
        then
        (bind ?rec (modify ?rec (max_horas_lab ?ml)))
    )

    (bind ?th (pregunta-cerrada ">> Que horario se ajusta mejor a su disponibilidad?" TRUE manyana tarde))
	(if (not(eq ?th nil))
        then
        (bind ?th-ins (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus ?th))))
        (bind ?rec (modify ?rec (tipo_horario ?th-ins)))
        else
        (bind ?th-ins-man (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus "manyana"))))
        (bind ?th-ins-tar (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus "tarde"))))
        (bind $?tipo-horario (create$))
        (bind ?tipo-horario (insert$ ?tipo-horario 1 ?th-ins-man))
        (bind ?tipo-horario (insert$ ?tipo-horario 2 ?th-ins-tar))
        (bind ?rec (modify ?rec (tipo_horario ?tipo-horario)))
    )

    (bind ?temasN (create$))
    (do-for-all-instances ((?t Especializado)) TRUE (bind ?temasN (insert$ ?temasN 1 (send ?t get-nombre_tema))))
    (bind ?numTem (pregunta-lista-numeros ">> Que temas especializados te interesan?" TRUE ?temasN))
    (if (not(eq ?numTem nil))
        then
        (bind $?temasI (create$))
        (loop-for-count (?i 1 (length$ ?numTem)) do
            (bind ?num (nth$ ?i ?numTem))
            (bind ?nomTem (nth$ ?num ?temasN))
            (bind ?tema-ins (find-instance ((?tem Especializado)) (eq ?tem:nombre_tema ?nomTem)))
            
            ;(printout t "numero " ?num crlf)
            ;(printout t "nombre " ?nomTem crlf)
            ;(printout t "instancia " ?tema-ins crlf)
            
            (bind ?temasI (insert$ ?temasI 1 ?tema-ins))
        )
        (bind ?rec (modify ?rec (tema_especializado ?temasI)))
    )

    (bind ?espN (create$))
    (do-for-all-instances ((?t Especialidad)) TRUE (bind ?espN (insert$ ?espN 1 (send ?t get-nombre_esp))))
    (bind ?numEsp (pregunta-numero ">> Que especialidad deseas acabar?" TRUE ?espN))
    (if (not(eq ?numEsp nil))
        then
        (bind ?nomEsp (nth$ ?numEsp ?espN))
        (bind ?esp-ins (find-instance ((?esp Especialidad)) (eq ?esp:nombre_esp (primera-mayus ?nomEsp))))
        
        ;(printout t "numero " ?numEsp crlf)
        ;(printout t "nombre " ?nomEsp crlf)
        ;(printout t "instancia " ?esp-ins crlf)
        
        (bind ?rec (modify ?rec (completar_especialidad ?esp-ins)))
    )

    (bind ?di (pregunta-cerrada ">> Que dificultad puedes asumir?" TRUE facil dificil))
	(if (not(eq ?th nil))
        then
        (bind ?rec (modify ?rec (dificultad ?di)))
    )    
    
    (bind ?comP (create$))
    (do-for-all-instances ((?t Competencia)) TRUE (bind ?comP (insert$ ?comP 1 (str-cat (sub-string 3 (str-length(send ?t get-nombre_comp)) (send ?t get-nombre_comp))))))
    (bind ?ordComP (sort-list ?comP))
    (bind ?numComp (pregunta-lista-numeros ">> Cuales son tus competencias favoritas?" TRUE ?ordComP))
    (if (not(eq ?numComp nil))
        then
        (bind $?compeI (create$))
        (loop-for-count (?i 1 (length$ ?numComp)) do
            (bind ?num (nth$ ?i ?numComp))
            
            (bind ?nomComp (nth$ ?num ?ordComP))
            ;(bind ?nivComp (sub-string (-(str-length(nth$ ?num ?ordComP))2) (-(str-length(nth$ ?num ?ordComP))1) (nth$ ?num ?ordComP)))
            (bind $?comp-ins (find-all-instances ((?comp Competencia)) (= (str-compare (sub-string 3 (str-length ?comp:nombre_comp) ?comp:nombre_comp) ?nomComp) 0)))
            
            (printout t "numero " ?num crlf)
            (printout t "nombre " ?nomComp crlf)
            ;(printout t "nivel " ?nivComp crlf)
            (printout t "instancia " ?comp-ins crlf)
            
            (bind ?compeI (insert$ ?compeI 1 ?comp-ins))
        )
        (bind ?rec (modify ?rec (competencias_preferidas ?compeI)))
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
    
    (printout t "num. restricciones: " ?nrest crlf)
    
    (assert (contador ok))
    (assert (nrestricciones ?nrest))
    (retract ?hecho1)
    (retract ?hecho2)
)

(defrule inferencia-preferencias "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (contador ok)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni))
    ?rec <- (respref (es_restriccion FALSE))
    
    =>

    ;;; TODO: inferencia de respref ;;;
    (printout t "Inferencia de preferencias" crlf)
    

    (assert(inferencia ok))
    (retract ?hecho)
)