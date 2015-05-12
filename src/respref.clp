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

(defrule entrada-inferencia
    ?hecho <- (contador ok)
    
    =>
    
    (printout t "Inferencia de preferencias" crlf)
    
    (assert (inf-comp))
    (assert (inf-esp))
    (assert (inf-dif))
    (assert (inf-nasig))
    (assert (inf-horas))
    (assert (inf-tema))
    (assert (inf-horario))
    (retract ?hecho)
)

(defrule inferencia-competencias
    ?hecho <- (inf-comp)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    ?pref <- (respref (es_restriccion FALSE) (competencias_preferidas $?cp))
    
    =>
    
    (printout t ">> Inferencia de preferencia de competencias" crlf)

    (bind $?notas (send ?exped get-notas_exp))
    
    (bind $?compe (create$)) ; competencias cursadas (con algun nivel N1-N3)
    
    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?conv (send ?not get-convocatoria_nota))
        (bind ?asig (send ?conv get-asignatura_conv))
        (bind $?com (send ?asig get-competencias))
        
        (loop-for-count (?j 1 (length$ ?com)) do
            (bind ?com-j (nth$ ?j ?com))
            (if (not (member ?com-j ?compe))
                then
                (bind ?nomCom (str-cat (sub-string 3 (str-length(send ?com-j get-nombre_comp)) (send ?com-j get-nombre_comp))))
                (bind $?comp-j-ins (find-all-instances ((?c Competencia)) (= (str-compare (sub-string 3 (str-length ?c:nombre_comp) ?c:nombre_comp) ?nomCom) 0)))
                (bind ?compe (insert$ ?compe 1 ?comp-j-ins))
            )
        )
    )
    
    (if (= (length$ ?cp) 0)
        then
        ; competencias cursadas de N1-3 (aunque no haya hecho todos los niveles)
        (bind ?pref (modify ?pref (competencias_preferidas ?compe)))
    )
    
    (assert (inf-comp ok))
    (retract ?hecho)
)

(defrule inferencia-especialidad
    ?hecho <- (inf-esp)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped) (especialidad ?esp))
    ?pref <- (respref (es_restriccion FALSE) (completar_especialidad $?ce))
    
    =>
    
    (printout t ">> Inferencia de preferencia de especialidad" crlf)

    (bind $?notas (send ?exped get-notas_exp))
    
    (bind $?espe (create$)) ; especialidad matriculada y especialidad a punto de acabar
    (bind $?espeCur (create$)) ; especialidades cursadas
    (bind $?nasigEs (create$)) ; numero de asignaturas cursadas de cada especialidad (mismas posiciones que $?espeCur)
    
    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?conv (send ?not get-convocatoria_nota))
        (bind ?asig (send ?conv get-asignatura_conv))
        ;(bind ?espA (send ?asig get-especialidad)) ;;; ESPECIALIDAD DE LA ASIGANTURA ;;;
        (bind ?espA (create$)) ;;; ESPECIALIDAD DE LA ASIGANTURA ;;;
        
        (if (not (member ?espA ?espeCur))
            then
            (bind ?espeCur (insert$ ?espeCur 1 ?espA))
            (bind ?nasigEs (insert$ ?nasigEs 1 1))
            else
            (bind ?ind (find-index ?espA ?espeCur))
            (bind ?nasigEs (replace$ ?nasigEs ?ind ?ind (+(nth$ ?ind ?nasigEs)1)))
        )
    )
    
    (if (= (length$ ?ce) 0)
        then
        ; especialidad de alumno (si la tiene) y especialidad casi acabada (si se da el caso)
        (bind ?espes (create$))
        
        (if (not(eq ?esp nil))
            then
            (bind ?espes (insert$ ?espes 1 ?esp))
        )
        
        (if (> (length$ ?nasigEs) 0)
            then
            (bind ?max 1)
            (loop-for-count (?i 2 (length$ ?nasigEs)) do
                (if (> (nth$ ?i ?nasigEs) (nth$ ?max ?nasigEs))
                    then
                    (bind ?max ?i)
                )
            )
            (bind ?espMax (nth$ ?max ?espeCur))
            (if (not(member ?espMax ?espes))
                then
                (bind ?espes (insert$ ?espes 1 espMax))
            )
        )
    
        (bind ?pref (modify ?pref (completar_especialidad ?espes)))
    )
    
    (assert(inf-esp ok))
    (retract ?hecho)
)

(defrule inferencia-dificultad "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (inf-dif)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    ?pref <- (respref (es_restriccion FALSE) (competencias_preferidas $?cp) (completar_especialidad $?ce) (dificultad ?d) 
                    (max_asigns ?ma) (max_horas_trabajo ?mht) (max_horas_lab ?mhl) (tema_especializado $?te) (tipo_horario $?th))
    
    =>
    
    (printout t ">> Inferencia de preferencia de dificultad" crlf)

    (bind $?notas (send ?exped get-notas_exp))
    
    (bind ?nasig 0) ; numero de asignaturas cursadas
    (bind $?cuatris (create$)) ; cuatris en los que ha cursado alguna asignatura
    (bind $?nasigCu (create$)) ; numero de asignaturas por cada cuatri cursado (mismas posiciones que $?cuatris)
    
    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?conv (send ?not get-convocatoria_nota))
        (bind ?asig (send ?conv get-asignatura_conv))
        (bind ?cuat (send ?conv get-cuatrimestre))
        
        (bind ?nasig (+ ?nasig 1))
    )
    
    (if (eq ?d nil)
        then
        ; dificultad?
    )
    
    (assert(inf-dif ok))
    (retract ?hecho)
)

(defrule inferencia-max-asigns "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (inf-nasig)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    ?pref <- (respref (es_restriccion FALSE) (max_asigns ?ma))
    
    =>
    
    (printout t ">> Inferencia de preferencia de maxAsigns" crlf)

    (bind $?notas (send ?exped get-notas_exp))
    
    (bind ?nasig 0) ; numero de asignaturas cursadas
    (bind $?cuatris (create$)) ; cuatris en los que ha cursado alguna asignatura
    (bind $?nasigCu (create$)) ; numero de asignaturas por cada cuatri cursado (mismas posiciones que $?cuatris)
    
    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?conv (send ?not get-convocatoria_nota))
        (bind ?asig (send ?conv get-asignatura_conv))
        (bind ?cuat (send ?conv get-cuatrimestre))
        
        (bind ?nasig (+ ?nasig 1))
        
        (if (not (member ?cuat ?cuatris))
            then
            (bind ?cuatris (insert$ ?cuatris 1 ?cuat))
            (bind ?nasigCu (insert$ ?nasigCu 1 1))
            else
            (bind ?ind (find-index ?cuat ?cuatris))
            (bind ?nasigCu (replace$ ?nasigCu ?ind ?ind (+(nth$ ?ind ?nasigCu)1)))
        )
    )
    
    (if (eq ?ma nil)
        then
        ; media de asignaturas/cuatri
        (bind ?mediaAs (div ?nasig (length$ ?cuatris)))
        (bind ?pref (modify ?pref (max_asigns ?mediaAs)))
    )
    
    (assert(inf-nasig ok))
    (retract ?hecho)
)

(defrule inferencia-horas "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (inf-horas)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    ?pref <- (respref (es_restriccion FALSE) (max_horas_trabajo ?mht) (max_horas_lab ?mhl))
    
    =>
    
    (printout t ">> Inferencia de preferencia de maxHoras y maxHorasLab" crlf)

    (bind $?notas (send ?exped get-notas_exp))
    
    (bind ?nhoras-teo 0) ; numero de horas de teoria cursadas
    (bind ?nhoras-lab 0) ; numero de horas de lab cursadas
    (bind ?nhoras-pro 0) ; numero de horas de problemas cursadas
    (bind $?cuatris (create$)) ; cuatris en los que ha cursado alguna asignatura
    (bind $?nasigCu (create$)) ; numero de asignaturas por cada cuatri cursado (mismas posiciones que $?cuatris)
    
    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?conv (send ?not get-convocatoria_nota))
        (bind ?asig (send ?conv get-asignatura_conv))
        (bind ?cuat (send ?conv get-cuatrimestre))
        (bind ?horT (send ?asig get-horas_teoria))
        (bind ?horL (send ?asig get-horas_lab))
        (bind ?horP (send ?asig get-horas_lab))
        
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
    )
    
    (if (eq ?mht nil)
        then
        ; media de horas de teoria/cuatri
        (bind ?mediaHT (div ?nhoras-teo (length$ ?cuatris)))
        (bind ?pref (modify ?pref (max_horas_trabajo ?mediaHT)))
    )
    (if (eq ?mhl nil)
        then
        ; media de horas de lab y prob/cuatri
        (bind ?mediaHL (div (+ ?nhoras-lab ?nhoras-pro) (length$ ?cuatris)))
        (bind ?pref (modify ?pref (max_horas_trabajo ?mediaHL)))
    )
    
    (assert(inf-horas ok))
    (retract ?hecho)
)

(defrule inferencia-tema "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (inf-tema)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    ?pref <- (respref (es_restriccion FALSE) (tema_especializado $?te))
    
    =>
    
    (printout t ">> Inferencia de preferencia de tema" crlf)

    (bind $?notas (send ?exped get-notas_exp))
    
    (bind $?temas (create$)) ; temas de las asignaturas cursadas
    (bind $?afins (create$)) ; temas afines a las asignaturas cursadas
    
    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?conv (send ?not get-convocatoria_nota))
        (bind ?asig (send ?conv get-asignatura_conv))
        (bind $?tem (send ?asig get-temas))
        
        (loop-for-count (?j 1 (length$ ?tem)) do
            (bind ?tem-j (nth$ ?j ?tem))
            (if (not (member ?tem-j ?temas))
                then
                (bind ?temas (insert$ ?temas 1 ?tem-j))
            )
            (if (eq (str-cat (class ?tem-j)) "Especializado")
                then
                (printout t "Tema Especializado! (tiene afines)" crlf)
                (bind $?temAf (send ?tem-j get-temas_afines))
                (loop-for-count (?k 1 (length$ ?temAf)) do
                    (bind ?tem-k (nth$ ?k ?temAf))
                    (if (not (member ?tem-k ?afines))
                        then
                        (bind ?afines (insert$ ?afines 1 ?tem-k))
                    )
                )
            )
        )
    )
    
    (if (= (length$ ?te) 0)
        then
        ; temas cursados y temas afines a los cursados
        (bind ?tems (insert$ ?afins 1 ?temas))
        (bind ?pref (modify ?pref (tema_especializado ?tems)))
    )
    
    (assert(inf-tema ok))
    (retract ?hecho)
)

(defrule inferencia-horario "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (inf-horario)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    ?pref <- (respref (es_restriccion FALSE) (tipo_horario $?th))
    
    =>
    
    (printout t ">> Inferencia de preferencia de tipo de horario" crlf)

    (bind $?notas (send ?exped get-notas_exp))
    
    (bind ?nasig 0) ; numero de asignaturas cursadas
    (bind $?cuatris (create$)) ; cuatris en los que ha cursado alguna asignatura
    (bind $?nasigCu (create$)) ; numero de asignaturas por cada cuatri cursado (mismas posiciones que $?cuatris)
    (bind $?temas (create$)) ; temas de las asignaturas cursadas
    
    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?conv (send ?not get-convocatoria_nota))
        (bind ?asig (send ?conv get-asignatura_conv))
        (bind ?cuat (send ?conv get-cuatrimestre))
        
        (bind ?nasig (+ ?nasig 1))
    )
    
    
    (if (= (length$ ?th) 0)
        then
        ; horario cuatri anterior (o todos los cuatris?)
    )
    
    (assert(inf-horario ok))
    (retract ?hecho)
)

(defrule fin-inferencia
    ?hecho1 <- (inf-comp ok)
    ?hecho2 <- (inf-esp ok)
    ?hecho3 <- (inf-dif ok)
    ?hecho4 <- (inf-nasig ok)
    ?hecho5 <- (inf-horas ok)
    ?hecho6 <- (inf-tema ok)
    ?hecho7 <- (inf-horario ok)
    
    =>
    
    (printout t "Fin inferencia" crlf)
    
    (assert(inferencia ok))
    (retract ?hecho1 ?hecho2 ?hecho3 ?hecho4 ?hecho5 ?hecho6 ?hecho7)
)