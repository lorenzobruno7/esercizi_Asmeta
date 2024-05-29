asm parcheggio

import ../../Library/StandardLibrary
import ../../Library/CTLlibrary

/*
Modellare in ASMETA il funzionamento del seguente sistema di parcheggio.
Il parcheggio è dotato di due telecamere, una installata all' ingresso del parcheggio ed una all'uscita dal parcheggio
di un semaforo che segnala, se verde, la disponibilità di posti liberi nel parcheggio. 

Per ogni auto che entra/esce, il sistema tiene informazione del numero delle auto parcheggiate. 
I posti sono distinti in posti destinati agli abbonati e posti a parcheggio libero. 
I posti liberi sono accessibili a tutti.
Quando questi posti si sono esauriti, il semaforo diventa giallo e l'accesso è concesso solo ad utenti con abbonamento. 
Appena ritorna la disponibilità di posti liberi, il semaforo viene messo a verde. 
Appena i posti destinati agli abbonati terminano, il semaforo diventa rosso ed impedisce completamente l'accesso.

Validare il modello attraverso 4 scenari
	- Uno che mostra il normale funzionamento del parcheggio.

	- Uno che mostra il passaggio del semaforo da verde a giallo

	- Uno che mostra il passaggio del semaforo da giallo a rosso

	- Uno che mostra il passaggio del semaforo da rosso a verde

Commentare gli scenari indicando i requisiti coperti da ciascun scenario.

Verificare (commentandole opportunamente) tre proprietà:

Una di raggiungibilità: che prima o poi il semaforo diventa rosso

Una di safety: che se non ci sono posti liberi ma ancora per abbonati, il semaforo è giallo

Una di liveness: che se il semaforo è rosso, prima o poi diventa verde

*/

signature:
enum domain StatoSemaforo = {VERDE | GIALLO | ROSSO}
enum domain TipologiaMacchina = {LIBERO | ABBONATO}

domain CapienzaParcheggio subsetof Integer

domain Semaforo subsetof Agent
domain Telecamera subsetof Agent

dynamic controlled statoSemaforo: Semaforo -> StatoSemaforo
dynamic controlled capienzaAttuale: CapienzaParcheggio

dynamic monitored macchina: TipologiaMacchina
dynamic monitored isEntrante: Boolean

static semaforo: Semaforo
static telecamera: Telecamera

definitions:
domain CapienzaParcheggio = {0 : 10}

rule r_Semaforo = 
	if capienzaAttuale >= 4 then
		statoSemaforo(self) := GIALLO
		else if capienzaAttuale < 4 then
		statoSemaforo(self) := VERDE
	else if capienzaAttuale = 10 then
		statoSemaforo(self) := ROSSO
	endif endif endif
	
rule r_Entrata($m in TipologiaMacchina) =
		if statoSemaforo(semaforo) = VERDE then 
			capienzaAttuale := capienzaAttuale + 1 
		else if statoSemaforo(semaforo) = GIALLO and $m = ABBONATO then
			capienzaAttuale := capienzaAttuale + 1
		else if statoSemaforo(semaforo) = ROSSO then skip
	 endif endif endif

rule r_Uscita = 
	if capienzaAttuale > 0 then
	capienzaAttuale := capienzaAttuale - 1
	endif
	

rule r_Telecamera = 
	if isEntrante = true and capienzaAttuale < 10 then
		r_Entrata[macchina]
	else if isEntrante = false then
		r_Uscita[]
	endif endif

//CTL

//Inviarianti
invariant over capienzaAttuale :  capienzaAttuale <= 10

main rule r_Main = 
	par
		program(semaforo)
		program(telecamera)
	endpar


default init s0:
function statoSemaforo($s in Semaforo) = VERDE
function capienzaAttuale = 0

agent Semaforo : r_Semaforo[]
agent Telecamera : r_Telecamera[]

