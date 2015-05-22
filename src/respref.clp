;;
;; Estructuras para la recogida de datos de restricciones/preferencias
;;

(defmodule respref "Módulo para la recogida de datos de restricciones/preferencias"
    (import MAIN ?ALL)
    (import consultas deffunction ?ALL)
    (import consultas deftemplate dni)
    (export ?ALL)
)


(deftemplate respref
    (slot es_restriccion)
    (multislot competencias_preferidas)
    (slot completar_especialidad)
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
    (printout t "A continuacion se le formularan una serie de preguntas sobre sus" crlf)
    (printout t "preferencias/restricciones para poder recomendarle asignaturas" crlf)
    (printout t crlf)
    
	(assert (ent-respref FALSE))
    (assert (ent-respref TRUE))
    (assert (respref (es_restriccion TRUE)))
    (assert (respref (es_restriccion FALSE)))
)

(defrule preguntas-respref "Modifica los hechos de ResPref segun lo que pida el alumno"
    ?hecho <- (ent-respref ?es-rest)
	(dni ?dni)
	?alumn <- (object (is-a Alumno) (id ?dni) (especialidad ?esp))  ; ?alumn es la instancia del alumno con id ?dni al que le queremos introducir las respref
    ?rec <- (respref (es_restriccion ?es-rest))

	=>

	(if (eq ?es-rest TRUE)
		then
		(progn (printout t "Introduccion de RESTRICCIONES" crlf) (assert (restrs ok)))
		else
		(progn (printout t "Introduccion de PREFERENCIAS" crlf) (assert (prefs ok)))
	)

    (bind ?ma (pregunta-rango "Cual es el numero maximo de asignaturas a matricular?" TRUE 1 6))
    (if (not(eq ?ma nil))
        then
        (bind ?rec (modify ?rec (max_asigns ?ma)))
    )

    (bind ?mh (pregunta-rango "Cual es el numero maximo de horas de dedicacion semanales?" TRUE 0 50))
    (if (not(eq ?mh nil))
        then
        (bind ?rec (modify ?rec (max_horas_trabajo ?mh)))
    )

    (bind ?ml (pregunta-rango "Cual es el numero maximo de horas de laboratorio/problemas semanales?" TRUE 0 50))
    (if (not(eq ?ml nil))
        then
        (bind ?rec (modify ?rec (max_horas_lab ?ml)))
    )

    (bind ?th (pregunta-cerrada "Que horario se ajusta mejor a su disponibilidad?" TRUE manyana tarde cualquiera))
	(if (not(eq ?th nil))
        then
        (if (eq 0 (str-compare ?th cualquiera))
            then
            (bind ?th-ins-man (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus "manyana"))))
            (bind ?th-ins-tar (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus "tarde"))))
            (bind $?tipo-horar (create$))
            (bind ?tipo-horar (insert$ ?tipo-horar 1 ?th-ins-man))
            (bind ?tipo-horar (insert$ ?tipo-horar 2 ?th-ins-tar))
            (bind ?rec (modify ?rec (tipo_horario ?tipo-horar)))
            else
            (bind ?th-ins (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus ?th))))
            (bind ?rec (modify ?rec (tipo_horario ?th-ins)))
        )
    )
    
    (if (not(eq ?esp [nil]))
        then
        ; el alumno tiene una especialidad
        (bind ?frase (str-cat (str-cat "Su especialidad es " (send ?esp get-nombre_esp)) ". Desea completar su especialidad?"))
        (bind ?bool (pregunta-cerrada ?frase TRUE si no))
        (if (eq ?bool si)
            then
            (bind ?rec (modify ?rec (completar_especialidad ?esp)))
        )
        else
        ; el alumno no tiene una especialidad --> preguntar cual quiere cursar
        (bind ?espN (create$))
        (do-for-all-instances ((?t Especialidad)) TRUE (bind ?espN (insert$ ?espN 1 (send ?t get-nombre_esp))))
        (bind ?numEsp (pregunta-numero "Que especialidad desea matricular?" TRUE ?espN))
        (if (not(eq ?numEsp nil))
            then
            (bind ?nomEsp (nth$ ?numEsp ?espN))
            (bind ?esp-ins (find-instance ((?e Especialidad)) (eq ?e:nombre_esp (primera-mayus ?nomEsp))))
            (bind ?rec (modify ?rec (completar_especialidad (nth$ 1 ?esp-ins))))
        )
    )

    (bind ?temasN (create$))
    (do-for-all-instances ((?t Especializado)) TRUE (bind ?temasN (insert$ ?temasN 1 (send ?t get-nombre_tema))))
    (bind ?numTem (pregunta-lista-numeros "Que temas especializados le interesan?" TRUE ?temasN))
    (if (not(eq ?numTem nil))
        then
        (bind $?temasI (create$))
        (loop-for-count (?i 1 (length$ ?numTem)) do
            (bind ?num (nth$ ?i ?numTem))
            (bind ?nomTem (nth$ ?num ?temasN))
            (bind ?tema-ins (find-instance ((?tem Especializado)) (eq ?tem:nombre_tema ?nomTem)))
            (bind ?temasI (insert$ ?temasI 1 ?tema-ins))
        )
        (bind ?rec (modify ?rec (tema_especializado ?temasI)))
    )

    (bind ?comP (create$))
    (do-for-all-instances ((?t Competencia)) TRUE (bind ?comP (insert$ ?comP 1 (str-cat (sub-string 3 (str-length(send ?t get-nombre_comp)) (send ?t get-nombre_comp))))))
    (bind ?ordComP (sort-list ?comP))
    (bind ?numComp (pregunta-lista-numeros "Cuales son sus competencias favoritas?" TRUE ?ordComP))
    (if (not(eq ?numComp nil))
        then
        (bind $?compeI (create$))
        (loop-for-count (?i 1 (length$ ?numComp)) do
            (bind ?num (nth$ ?i ?numComp))

            (bind ?nomComp (nth$ ?num ?ordComP))
            (bind $?comp-ins (find-all-instances ((?comp Competencia)) (= (str-compare (sub-string 3 (str-length ?comp:nombre_comp) ?comp:nombre_comp) ?nomComp) 0)))
            (bind ?compeI (insert$ ?compeI 1 ?comp-ins))
        )
        (bind ?rec (modify ?rec (competencias_preferidas ?compeI)))
    )
    
    (printout t crlf)

    (retract ?hecho)
)

(defrule contador-restricciones
    ?hecho1 <- (prefs ok)
    ?hecho2 <- (restrs ok)
    ?rest <- (respref (es_restriccion TRUE) (competencias_preferidas $?cp) (completar_especialidad ?ce) (dificultad ?d)
                    (max_asigns ?ma) (max_horas_trabajo ?mht) (max_horas_lab ?mhl) (tema_especializado $?te) (tipo_horario $?th))

    =>

    ;(printout t "Contador de restricciones" crlf)
    (bind ?nrest 0)
    (if (> (length$ ?cp) 0) then (bind ?nrest (+ ?nrest 1)))
    (if (neq ?ce nil) then (bind ?nrest (+ ?nrest 1)))
    ;(if (neq ?d nil) then (bind ?nrest (+ ?nrest 1)))
    (if (> (length$ ?te) 0) then (bind ?nrest (+ ?nrest 1)))
    (if (> (length$ ?th) 0) then (bind ?nrest (+ ?nrest 1))) ;por defecto ?th tiene asignado los dos horarios posibles

    ;(printout t ">> num. restricciones: " ?nrest crlf)

    ;Restricciones que no se pueden comprobar hasta el final
    (bind ?nrest-final 0)
    (if (neq ?ma nil) then (bind ?nrest-final (+ ?nrest-final 1)))
    (if (neq ?mht nil) then (bind ?nrest-final (+ ?nrest-final 1)))
    (if (neq ?mhl nil) then (bind ?nrest-final (+ ?nrest-final 1)))


    (assert (contador ok))
    (assert (nrestricciones ?nrest ?nrest-final))
    (retract ?hecho1)
    (retract ?hecho2)
)

(defrule inferencia-preferencias "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (contador ok)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped) (especialidad ?esp))

    =>
    
    (printout t "=====================================================================" crlf)
    (printout t "=                            Inferencia                             =" crlf)
    (printout t "=====================================================================" crlf)
    (printout t crlf)
    
    (printout t "Los siguientes dados se han inferido a partir de su Expediente:" crlf)

    (bind $?notas (send ?exped get-notas_exp))

    (bind ?nasig 0) ; numero de asignaturas cursadas
    (bind ?ncred 0) ; numero de creditos cursados
    (bind ?nhoras-teo 0) ; numero de horas de teoria cursadas
    (bind ?nhoras-lab 0) ; numero de horas de lab cursadas
    (bind ?nhoras-pro 0) ; numero de horas de problemas cursadas
    (bind $?cuatris (create$)) ; cuatris en los que ha cursado alguna asignatura
    (bind $?nasigCu (create$)) ; numero de asignaturas por cada cuatri cursado (mismas posiciones que $?cuatris)
    (bind $?temas (create$)) ; temas de las asignaturas cursadas
    (bind $?afins (create$)) ; temas afines a las asignaturas cursadas
    (bind $?compe (create$)) ; competencias cursadas (con algun nivel N1-N3)
    (bind $?espe (create$)) ; especialidad matriculada y especialidad a punto de acabar
    (bind $?espeCur (create$)) ; especialidades cursadas
    (bind $?nasigEs (create$)) ; numero de asignaturas cursadas de cada especialidad (mismas posiciones que $?espeCur)
    (bind $?horarioC (create$)) ; horarios en cada cuatri (+ si es de tardes, - si es de mañanas)
    (bind ?nfacil 0) ; numero de asignaturas faciles cursadas
    (bind ?ndificil 0) ; numero de asignaturas dificiles cursadas
    (bind ?sfacil 0) ; numero de asignaturas faciles suspendidas
    (bind ?sdificil 0) ; numero de asignaturas dificiles suspendidas
    (bind ?peor-nota-dificil 10) ; peor nota de una asignatura dificil

    (loop-for-count (?i 1 (length$ ?notas)) do
        (bind ?not (nth$ ?i ?notas))
        (bind ?conv (send ?not get-convocatoria_nota))
        (bind ?asig (send ?conv get-asignatura_conv))
        (bind ?cuat (send ?conv get-cuatrimestre))
        (bind $?tem (send ?asig get-temas))
        (bind ?cred (send ?asig get-num_creditos))
        (bind ?horT (send ?asig get-horas_teoria))
        (bind ?horL (send ?asig get-horas_lab))
        (bind ?horP (send ?asig get-horas_prob))
        (bind $?com (send ?asig get-competencias))
        (bind $?espA nil)
        (if (eq (str-cat (class ?asig)) "Especializada")
            then
            (bind $?espA (send ?asig get-especialidad_asig))
        )
        (bind ?horaI (send ?conv get-horario_conv))
        (bind ?horaS (send ?horaI get-horario))
        (bind ?aprob (send ?asig get-aprobados_ant))
        (bind ?nota (send ?not get-nota))

        (bind ?nasig (+ ?nasig 1))
        (bind ?ncred (+ ?nasig ?cred))
        (bind ?nhoras-teo (+ ?nhoras-teo ?horT))
        (bind ?nhoras-lab (+ ?nhoras-lab ?horL))
        (bind ?nhoras-pro (+ ?nhoras-pro ?horP))

        (if (not (member ?cuat ?cuatris))
            then
            (bind ?cuatris (insert$ ?cuatris 1 ?cuat))
            (bind ?nasigCu (insert$ ?nasigCu 1 1))
            (if (=(str-compare ?horaS "Tarde")0)
                then
                (bind ?horarioC (insert$ ?horarioC 1 1))
                else
                (bind ?horarioC (insert$ ?horarioC 1 -1))
            )

            else
            (bind ?ind (find-index ?cuat ?cuatris))
            (bind ?nasigCu (replace$ ?nasigCu ?ind ?ind (+(nth$ ?ind ?nasigCu)1)))
            (if (=(str-compare ?horaS "Tarde")0)
                then
                (bind ?horarioC (replace$ ?horarioC ?ind ?ind (+(nth$ ?ind ?horarioC)1)))
                else
                (bind ?horarioC (replace$ ?horarioC ?ind ?ind (-(nth$ ?ind ?horarioC)1)))
            )
        )

        (loop-for-count (?j 1 (length$ ?tem)) do
            (bind ?tem-j (nth$ ?j ?tem))
            (if (not (member ?tem-j ?temas))
                then
                (bind ?temas (insert$ ?temas 1 ?tem-j))
            )
            (if (eq (str-cat (class ?tem-j)) "Especializado")
                then
                (bind $?temAf (send ?tem-j get-temas_afines))
                (loop-for-count (?k 1 (length$ ?temAf)) do
                    (bind ?tem-k (nth$ ?k ?temAf))
                    (if (not (member ?tem-k ?afins))
                        then
                        (bind ?afins (insert$ ?afins 1 ?tem-k))
                    )
                )
            )
        )

        (loop-for-count (?j 1 (length$ ?com)) do
            (bind ?com-j (nth$ ?j ?com))
            (if (not (member ?com-j ?compe))
                then
                (bind ?nomCom (str-cat (sub-string 3 (str-length(send ?com-j get-nombre_comp)) (send ?com-j get-nombre_comp))))
                (bind $?comp-j-ins (find-all-instances ((?c Competencia)) (= (str-compare (sub-string 3 (str-length ?c:nombre_comp) ?c:nombre_comp) ?nomCom) 0)))
                (bind ?compe (insert$ ?compe 1 ?comp-j-ins))
            )
        )

        (if (not (eq ?espA nil))
            then
            (loop-for-count (?j 1 (length$ ?espA)) do
                (bind ?esp-j (nth$ ?j ?espA))
                    then
                (if (not (member ?esp-j ?espeCur))
                    then
                    (bind ?espeCur (insert$ ?espeCur 1 ?esp-j))
                    (bind ?nasigEs (insert$ ?nasigEs 1 1))
                    else
                    (bind ?ind (find-index ?esp-j ?espeCur))
                    (bind ?nasigEs (replace$ ?nasigEs ?ind ?ind (+(nth$ ?ind ?nasigEs)1)))
                )
            )
        )
        

        (if (> ?aprob 70)
            then
            ; asignatura facil
            (bind ?nfacil (+ ?nfacil 1))
            (if (< ?nota 5) then (bind ?sfacil (+ ?sfacil 1)))
            else
            ; asignatura dificil
            (bind ?ndificil (+ ?ndificil 1))
            (if (< ?nota 5) then (bind ?sdificil (+ ?sdificil 1)))
            (if (< ?nota ?peor-nota-dificil) then (bind ?peor-nota-dificil ?nota))
        )
    )
    (bind ?nhoras-teo (/ ?nhoras-teo 18))
    (bind ?nhoras-lab (/ ?nhoras-lab 18))
    (bind ?nhoras-pro (/ ?nhoras-pro 18))

    (assert (inf-comp $?compe p))
    (assert (inf-tema $?temas p $?afins))
    (assert (inf-esp $?nasigEs p $?espeCur))
    (assert (inf-horario $?horarioC p $?cuatris))
    (assert (inf-horas ?nhoras-teo ?nhoras-lab ?nhoras-pro $?cuatris))
    (assert (inf-nasig ?nasig p $?cuatris))
    (assert (inf-dif ?nfacil ?ndificil ?sfacil ?sdificil ?peor-nota-dificil))
    (assert (inf-curso))
    (retract ?hecho)
)

(deffunction muestra-nombres-competencias
    ($?cp)

    (bind $?compN (create$))
    (loop-for-count (?i 1 (length$ ?cp)) do
        (bind ?nom (send (nth$ ?i ?cp) get-nombre_comp))
        (if (not (member ?nom ?compN))
            then
            (bind $?compN (insert$ ?compN 1 ?nom))
        )
    )
    
    (bind ?primer TRUE)
    (loop-for-count (?i 1 (length$ ?compN)) do
        (if (eq ?primer FALSE) then (printout t ", "))
        (printout t (sub-string 3 (str-length (nth$ ?i ?compN)) (nth$ ?i ?compN)))
        (bind ?primer FALSE)
    )
    (printout t crlf)
)

(defrule inferencia-competencias
    ?hecho <- (inf-comp $?compe p)
    ?pref <- (respref (es_restriccion FALSE) (competencias_preferidas $?cp))

    =>
    
    (if (= (length$ ?cp) 0)
        then
        ; competencias cursadas de N1-3 (aunque no haya hecho todos los niveles)
        (bind ?pref (modify ?pref (competencias_preferidas ?compe)))
        
        (printout t " * Competencias: ")
        (muestra-nombres-competencias ?compe)
    )

    (assert (inf-comp ok))
    (retract ?hecho)
)

(defrule inferencia-especialidad
    ?hecho <- (inf-esp $?nasigEs p $?espeCur)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped) (especialidad ?esp))
    ?pref <- (respref (es_restriccion FALSE) (completar_especialidad ?ce))

    =>

    (if (not(eq ?ce [nil]))
        then
        ; especialidad de alumno (si la tiene) y especialidad casi acabada (si se da el caso)

        (if (not(eq ?esp [nil]))
            then
            (bind ?pref (modify ?pref (completar_especialidad ?esp)))
            (printout t " * Su especialidad matriculada: " (send ?esp get-nombre_esp) crlf)
            else
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
                (bind ?pref (modify ?pref (completar_especialidad ?espMax)))
                (printout t " * Sin especialidad matriculada, pero ha cursado varias asignaturas de: " (send ?espMax get-nombre_esp) crlf)
                else
                (printout t " * No se puede inferir una especialidad" crlf)
            )
        )
    )

    (assert(inf-esp ok))
    (retract ?hecho)
)

(defrule inferencia-dificultad "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (inf-dif ?nfacil ?ndificil ?sfacil ?sdificil ?peor-nota-dificil)
    ?pref <- (respref (es_restriccion FALSE) (dificultad ?d))

    =>
    (if (eq ?d nil)
        then
        (if (and (eq ?sfacil 0) (eq ?sdificil 0))
            then
            ; todo aprobado --> dificultad dificil
            (bind ?d "Dificil")
            else
            (if (> ?sfacil 0)
                then
                ; alguna facil suspendida --> dificultad facil
                (bind ?d "Facil")
                else
                ; alguna dificil suspendida (todas las faciles aprobadas)
                (if (< ?peor-nota-dificil 4)
                    then
                    (bind ?d "Facil")
                    else
                    (bind ?d "Dificil")
                )
            )
        )
        (bind ?pref (modify ?pref (dificultad ?d)))
        
        (printout t " * Dificultad: " ?d crlf)
    )

    (assert(inf-dif ok))
    (retract ?hecho)
)

(defrule inferencia-max-asigns "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (inf-nasig ?nasig p $?cuatris)
    ?pref <- (respref (es_restriccion FALSE) (max_asigns ?ma))

    =>
    (if (eq ?ma nil)
        then
        ; media de asignaturas/cuatri
        (bind ?mediaAs (div ?nasig (length$ ?cuatris)))
        (bind ?pref (modify ?pref (max_asigns ?mediaAs)))
        (printout t " * Num max asignaturas: " ?mediaAs crlf)
    )

    (assert(inf-nasig ok))
    (retract ?hecho)
)

(defrule inferencia-horas "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (inf-horas ?nhoras-teo ?nhoras-lab ?nhoras-pro $?cuatris)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    ?pref <- (respref (es_restriccion FALSE) (max_horas_trabajo ?mht) (max_horas_lab ?mhl))

    =>
    (if (eq ?mht nil)
        then
        ; media de horas de teoria/cuatri
        (bind ?mediaHT (div ?nhoras-teo (length$ ?cuatris)))
        (bind ?pref (modify ?pref (max_horas_trabajo ?mediaHT)))
        (printout t " * Max horas dedicacion semanal: " ?mediaHT crlf)
    )
    (if (eq ?mhl nil)
        then
        ; media de horas de lab y prob/cuatri
        (bind ?mediaHL (div (+ ?nhoras-lab ?nhoras-pro) (length$ ?cuatris)))
        (bind ?pref (modify ?pref (max_horas_lab ?mediaHL)))
        (printout t " * Max horas lab/prob semanal: " ?mediaHL crlf)
    )

    (assert(inf-horas ok))
    (retract ?hecho)
)

(defrule inferencia-tema "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (inf-tema $?temas p $?afins)
    ?pref <- (respref (es_restriccion FALSE) (tema_especializado $?te))

    =>

    (if (= (length$ ?te) 0)
        then
        ; temas cursados y temas afines a los cursados
        (bind ?tems (insert$ ?afins 1 ?temas))
        (bind ?pref (modify ?pref (tema_especializado ?tems)))
        
        (bind $?temaN (create$))
        (loop-for-count (?i 1 (length$ ?tems)) do
            (bind ?nom (send (nth$ ?i ?tems) get-nombre_tema))
            (if (not (member ?nom ?temaN))
                then
                (bind $?temaN (insert$ ?temaN 1 ?nom))
            )
        )
        
        (printout t " * Temas: ")
        (bind ?primer TRUE)
        (loop-for-count (?i 1 (length$ ?temaN)) do
            (if (eq ?primer FALSE) then (printout t ", "))
            (printout t (nth$ ?i ?temaN))
            (bind ?primer FALSE)
        )
        (printout t crlf)
    )

    (assert(inf-tema ok))
    (retract ?hecho)
)

(defrule inferencia-horario "Infiere restricciones/preferencias segun el expediente"
    ?hecho <- (inf-horario $?horarioC p $?cuatris)
    ?pref <- (respref (es_restriccion FALSE) (tipo_horario $?th))

    =>

    (if (= (length$ ?th) 0)
        then
        ; horario cuatri anterior
        (bind ?ordC (sort-list ?cuatris))
        (bind ?ultimoC (nth$ (length ?ordC) ?ordC))
        (bind ?ind (find-index ?ultimoC ?cuatris))
        (bind ?hora (nth$ ?ind ?horarioC))
        (if (or (eq ?hora 0) (> ?hora 0))
            then
            (bind ?th (insert$ ?th 1 (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus "tarde")))))
        )
        (if (or (eq ?hora 0) (< ?hora 0))
            then
            (bind ?th (insert$ ?th 1 (find-instance ((?ins Horario)) (eq ?ins:horario (primera-mayus "manyana")))))
        )
        (bind ?pref (modify ?pref (tipo_horario ?th)))
        
        (printout t " * Tipo de horario: " (send (nth$ 1 ?th) get-horario))
        (if (> (length$ ?th) 1) then (printout t (send (nth$ 2 ?th) get-horario)))
        (printout t crlf)
    )

    (assert(inf-horario ok))
    (retract ?hecho)
)


(deffunction curso-a-int
    (?cur)

    (switch ?cur
        (case primero then (return 1))
        (case segundo then (return 2))
        (case tercero then (return 3))
        (case cuarto then (return 4))
    )
)

(defrule inferencia-curso
    ?hecho <- (inf-curso)
    (dni ?dni)
    ?alumn <- (object (is-a Alumno) (id ?dni) (expediente_alumno ?exped))
    =>

    (bind ?notas (send ?exped get-notas_exp))
    (bind ?max-curso 0)
    (progn$ (?ins ?notas) ;encuentro el curso más superior que ha alcanzado el alumno
        (if (> (curso-a-int (send (send (send ?ins get-convocatoria_nota) get-asignatura_conv) get-curso)) ?max-curso)
            then
            (bind ?max-curso (curso-a-int (send (send (send ?ins get-convocatoria_nota) get-asignatura_conv) get-curso)))
        )
    )

    (printout t " * Curso: " ?max-curso crlf)
    
    (retract ?hecho)
    (assert (curso ?max-curso))
    (assert (inf-curso ok))
)

(defrule fin-inferencia
    ?hecho1 <- (inf-comp ok)
    ?hecho2 <- (inf-esp ok)
    ?hecho3 <- (inf-dif ok)
    ?hecho4 <- (inf-nasig ok)
    ?hecho5 <- (inf-horas ok)
    ?hecho6 <- (inf-tema ok)
    ?hecho7 <- (inf-horario ok)
    ?hecho8 <- (inf-curso ok)

    =>
    
    (printout t crlf)
    
    (retract ?hecho1 ?hecho2 ?hecho3 ?hecho4 ?hecho5 ?hecho6 ?hecho7 ?hecho8)

    (focus abstraccion)
)