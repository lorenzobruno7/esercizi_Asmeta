asm controlloreProcessi

import ../../Library/StandardLibrary
import ../../Library/CTLlibrary

/*Si consideri un sistema ad agenti composto da un controllare e da 2 processi. 
Il controllore è un agente; ogni processo è un agente.
Ogni processo può essere in stato WAITING, RUNNING o DEAD.
Ogni processo ha associato un tempo nell’intervallo [1,3] che indica la durata che manca al suo completamento.
Il controllore ed i processi sono attivi in modo alternato: ad ogni passo è attivo (running) o il controllore oppure uno dei processi.

Si modelli in ASMETA la seguente comportamento:
•	Il programma del controllore è il seguente: 
		(1) se non è attivo non fa niente, altrimenti
		(2) sceglie il processo in stato WAITING con tempo minimo e lo rende attivo.
•	Il comportamento di ogni processo è il seguente: 
		se il processo non è attivo (WAITING o DEAD) non fa niente,
		altrimenti (se RUNNING)
			(1) se il tempo d'esecuzione del processo è maggiore di 0, il tempo viene decrementato di un'unità
			(2) se il tempo d'esecuzione del processo è uguale a 0, il processo diventa DEAD e passa il controllo al controllore.
•	Nello stato inziale è attivo il controllore e tutti i processi sono in attesa.
Validare il modello attraverso tre scenari, costruiti a scelta ed opportunamente commentati (uno di safety, uno di raggiungibilità, uno di liveness)
Verificare le seguenti proprietà: 

*/

signature:
enum domain StatoProcesso = {WAITING | RUNNING | DEAD}

domain Processo subsetof Agent
domain Controllore subsetof Agent

domain TempoCompletamento subsetof Integer

dynamic controlled tempoRestante: Processo -> TempoCompletamento
dynamic controlled statoProcesso: Processo -> StatoProcesso
dynamic controlled statoControllore: Controllore -> StatoProcesso

static processo1: Processo
static processo2: Processo
static controllore: Controllore


definitions:
domain TempoCompletamento = {0 : 3}

rule r_processo = 
	if statoProcesso(self) = RUNNING then
		if (tempoRestante(self)) > 0 then 
			tempoRestante(self) := tempoRestante(self) - 1
		else if (tempoRestante(self)) = 0 then
			par
				statoProcesso(self) := DEAD
				statoControllore(controllore) := RUNNING
			endpar
	endif endif endif

//Qua dobbiamo prendere un processo con una choose e lo confrontiamo con gli altri processi attraverso una forall che ovviamente non siano uguali a quello scelto
rule r_controllore = 
	if statoControllore(self) = RUNNING then
		choose $p1 in Processo with statoProcesso($p1) = WAITING do
		//Questo è il modo di comparare dei valori che rispettino una condizione -> implies e metti la condizione e ti sei risolto i problemi
			forall $p2 in Processo with $p2 != $p1 and statoProcesso($p2) = WAITING implies tempoRestante($p1) <= tempoRestante($p2) do
			par
			//Attenzione a fare la verifica del $p1 scelto con tutti i $p2 e cambiare lo stato a $p1 e non a $p2 perché $p2 essendo una forall lo farà per tutti
				statoProcesso($p1) := RUNNING
				tempoRestante($p1) := 3
				statoControllore(controllore) := DEAD
			endpar
	endif
	

//In ogni stato o è attivo il controllore o è attivo un processo
//Safety per definizione, ovvero cose brutte non accadono, ovvero non accade la cosa peggiore che sono tutti running
CTLSPEC ag(not((statoControllore(controllore) = RUNNING) and (exist $p in Processo with statoProcesso($p) = RUNNING)))

//Al massimo un solo processo è nello stato RUNNING
CTLSPEC ag(not(forall $p in Processo with statoProcesso($p) = RUNNING))

//Esiste uno stato in cui tutti i processi sono DEAD ed il controllore è attivo
CTLSPEC (ef((forall $p in Processo with statoProcesso($p) = DEAD) and statoControllore(controllore) = RUNNING))

//Se nessun processo è nello stato di RUNNING, allora il controllore è attivo
CTLSPEC (ag((forall $p in Processo with statoProcesso($p) != RUNNING) implies statoControllore(controllore) = RUNNING))

//Trova un cammino che porta il sistema ad uno stato in cui i due processi sono DEAD (Reachability Property)
CTLSPEC (ef((forall $p in Processo with statoProcesso($p) = DEAD)))

//Il tempo di esecuzione rimanente ad ogni processo running è al massimo pari 3
CTLSPEC(ag((forall $p in Processo with statoProcesso($p) = RUNNING ) implies ag(tempoRestante($p) <= 3))  )

//Se un processo è DEAD, il tuo tempo di esecuzione rimanente è nullo
CTLSPEC(ag((forall $p in Processo with statoProcesso($p) = DEAD ) implies ag(tempoRestante($p) = 0)))

//Se il controllore è attivo, nello stato successivo almeno un processo è running
CTLSPEC af(statoControllore(controllore) = RUNNING implies ax((exist $p in Processo with statoProcesso($p) = RUNNING)))

//Un processo è DEAD solo se prima è stato running o waiting con controllore attivo.
CTLSPEC ag((forall $p in Processo with statoProcesso($p) != DEAD) and statoControllore(controllore) = RUNNING implies af(statoProcesso($p) = DEAD))

//Un processo è waiting, prima o poi diventa running (LIVENESS DA SLIDE)
CTLSPEC ag( (forall $p in Processo with statoProcesso($p) = WAITING) implies ef(statoProcesso($p) = RUNNING))



main rule r_Main =
	par
		forall $p in Processo with true do program($p)
		program(controllore)
	endpar


default init s0:
//Settiamo lo stato dei processi a WAITING con tempo a 3 e lo stato del Controllore a RUNNING
function statoProcesso($p in Processo) = WAITING
function tempoRestante($p in Processo) = 3
function statoControllore($c in Controllore) = RUNNING
//Associamo agli agenti la rule
agent Processo : r_processo[]
agent Controllore : r_controllore[]
