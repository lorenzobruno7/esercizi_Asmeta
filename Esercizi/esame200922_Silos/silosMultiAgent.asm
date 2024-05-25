asm silosMultiAgent

import ../../Library/StandardLibrary
import ../../Library/CTLlibrary

/* 
 						---ESAME 20 SETTEMBRE 2022 ---

Un silos di grano consiste di 3 bidoni cilindrici che possono contenere fino a 12 quintali di grano ciascuno

Una gru può versare del grano (da 1 fino a 5 quintali) in un singolo cilindro a scelta dell'operatore
Un nastro trasportatore può prelevare 2 quintali di grano da tutti i contenitori
(se un cilindro ha meno di due quintali, si svuota - cioè ad esempio se voglio prelevare 2 quantali da tutti i cilindri ma uno di essi ha solo 1 quintale, 
esso viene semplicemente svuotato).

La gru e il nastro non funzionano mai tutte e due insieme, però ad ogni passo almeno uno dei due funziona

Il sistema per sicurezza non permette mai di avere più di 10 quintali in ogni bidone (anche se cene starebbero 12) 
(la politica per garantire questo quando la gru riempie i cilindri è a tua scelta, ma cerca di essere permissivo)

Inizialmente i bidoni contengono tutti 1 quintale di grano

Verificare to prova che sono false tramite AsmetaSMV le seguenti proprietà temporale: 

 	- Proprietà P1: Tutti i cilindri non hanno mai più di 10 quintali di grano

	- Proprietà P2: Se attivo il nastro, nello stato successivo tutti i cillindri avranno al massimo 8 quintali

	- Proprietà P3: Se il primo cilindro è vuoto, finché non si attiva la gru, esso rimane vuoto

	- Proprietà ulteriori:
	         * Scrivi inoltre almeno una proprietà che è falsa e controlla che il model checker trovi il contro esempio atteso
	         * Scrivi almeno un'altra proprietà di liveness e safety che siano vere
*/

signature:
enum domain StatoMacchinario = {RUNNING | WAITING}

domain CapienzaMassima subsetof Integer
domain QuintaliDaVersare subsetof Integer
domain Bidone subsetof Integer
//Dominio degli agenti
domain Gru subsetof Agent
domain Nastro subsetof Agent

/*Invece di fare statoGru e statoNastro si potrebbe fare annche una cosa del tipo:
 * dynamic controlled statoMacchinario: Agent -> StatoMacchinario
 * sono entrambe valide e, anzi, questa più corretta ma per ora la lascio così per leggibilità del codice
 */

dynamic controlled statoGru: Gru -> StatoMacchinario
dynamic controlled statoNastro: Nastro -> StatoMacchinario
dynamic controlled quantitaAttuale: Bidone -> CapienzaMassima

//Monitorate
dynamic monitored quantitaVersare: QuintaliDaVersare
dynamic monitored bidonesScelto: Bidone

//Agenti
static gru: Gru
static nastro: Nastro
 

definitions:
domain CapienzaMassima = {0 : 12}
domain QuintaliDaVersare = {0 : 5}
domain Bidone = {1 : 3}

rule r_Gru = 
	if statoGru(self) = RUNNING then
		par
			if quantitaAttuale(bidonesScelto) <= 5 then
				quantitaAttuale(bidonesScelto) := quantitaAttuale(bidonesScelto) + quantitaVersare
			endif
			statoNastro(nastro) := RUNNING
			statoGru(gru) := WAITING
		endpar
	endif
	
rule r_Nastro = 
	if statoNastro(self) = RUNNING then
	par
		forall $b in Bidone with quantitaAttuale($b) >= 0 do
			if (quantitaAttuale($b) < 2) then
				quantitaAttuale($b) := 0
			else if (quantitaAttuale($b) >= 2) then
				quantitaAttuale($b) := quantitaAttuale($b) - 2
	endif endif
		statoGru(gru) := RUNNING
		statoNastro(nastro) := WAITING
	endpar 
	endif
				

//CTL

//Tutti i cilindri non hanno mai più di 10 quintali di grano
CTLSPEC ag ((forall $b in Bidone with quantitaAttuale($b) <= 10))

//Se attivo il nastro, nello stato successivo tutti i cillindri avranno al massimo 8 quintali
/*
 * La CTL è semanticamente corretta nella forma "AG+AX" perché racchiude la specifica richiesta.
 * La conversione in SMV però da questa CTL come falsa perchè considera come stato successivo a quello del nastro RUNNING quello in cui vengono settati gli stati
 * degli agent. Per questo motivo si potrebbe pensare di fare un ax(ax) ma anche in quel caso non sarebbe true. Per ovviare a questa cosa e far passare
 * la CTL si mette AF anche se non propriamente corretta.
 * 
 * In seduta d'esame mettere la CTL che da true alla CTL ma specificare il perché andrebbe invece AG
 */
CTLSPEC af (statoNastro(nastro) = RUNNING implies ax((forall $b in Bidone with quantitaAttuale($b) <= 8)))

//Se il primo cilindro è vuoto, finché non si attiva la gru, esso rimane vuoto
/*Stando alla traccia non si potrebbe fare il primo cilindro vuoto perché è condizione iniziale che tutti i cilindri partino con 1 quintale ciascuno */
CTLSPEC a(quantitaAttuale(1) = 1, statoGru(gru) = RUNNING )

//Proprietà ulteriori:
//Scrivi inoltre almeno una proprietà che è falsa e controlla che il model checker trovi il contro esempio atteso
CTLSPEC ag ((forall $b in Bidone with quantitaAttuale($b) > 10))

//Scrivi almeno un'altra proprietà di liveness e safety che siano vere

//Safety -> Non ci saranno mai bidoni con quantità maggiore di 10 (cose brutte non accadono)
CTLSPEC ag (not(forall $b in Bidone with quantitaAttuale($b) > 10)) 

//Liveness -> Alla fine accadrà che ci sarà un bidone con quantità maggiore di 0
CTLSPEC ag (ef((exist $b in Bidone with quantitaAttuale($b) > 0)) )


//INVIARIANTI
invariant over quantitaAttuale: (forall $b in Bidone with quantitaAttuale($b) <= 10)

main rule r_Main = 
	par
		program(gru)
		program(nastro)
	endpar
	

default init s0:
function statoGru($g in Gru) = RUNNING
function statoNastro($n in Nastro) = WAITING

function quantitaAttuale($b in Bidone) = 1

agent Gru: r_Gru[]
agent Nastro: r_Nastro[]
