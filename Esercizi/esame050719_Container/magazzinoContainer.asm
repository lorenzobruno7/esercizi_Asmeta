asm magazzinoContainer

import ../../Library/StandardLibrary
import ../../Library/CTLlibrary

/* 

*** Esame del 5 Luglio 2019 (Laboratorio) ***

 REQUISITI
 Scrivere una specifica che modelli il funzionamento di un magazzino di container utilizzibali per stivare merce.
 Il magazzino ha 25 container disposti a 5 per fila e ciascuno numerato da una coppia di valori (i,j) con i
 relativo alla riga in cui è parcheggiato il container, e j la colonna. In ogni momento è possibile selezionare un
 container libero per stivare la merce.
 I container occupati da merce vengono vuotati secondo una politica descritta sotto.

 MODELLO ASMETAL
 Ad ogni passo di simulazione:
 - l’utente seleziona un container vuoto da poter riempire;
 - tutti i container occupati vengono vuotati con probabilità del 10% se si trovano sulla prima riga, del 20%
 se si trovano sulla seconda riga, del 30% se si trovano sulla terza riga, del 40% se si trovano in quarta fila e del 50% se si trovano in quinta fila.
 All’inizio tutti i container sono liberi.

 SCENARI
 Specificare in Avalla uno scenario che riproduca la seguente situazione: tutti i container sono occupati tranne
 quello di posto (2,3), questo viene selezionato per essere riempito e il suo stato diventa occupato.
 Specificare un secondo scenario a scelta che mostri l’ adeguatezza del modello rispetto ai requisiti.

 PROPRIETÀ CTL
 Specificare tramite AsmetaSMV una proprietà temporale che verifichi che:
 - esiste uno stato in cui tutti i contanier sono occupati;
 - esiste uno stato a partire dal quale inizia un cammino in cui tutti i container sono occupati.
Trovare tramite model checking un cammino che porti in uno stato in cui i container (1,2) e (1,5) sono occupati.
*/

signature:
//Dominio per lo stato del container
enum domain StatoContainer = {FULL | EMPTY}
//Domini per righe, colonnee 
domain Riga subsetof Integer
domain Colonna subsetof Integer
domain Probabilita subsetof Integer

dynamic controlled riga: Riga
dynamic controlled colonna: Colonna
//Questa funzione, data la riga e colonna che identifica il container ci dice il suo stato
dynamic controlled container: Prod(Riga,Colonna) -> StatoContainer

dynamic monitored rigaScelta: Riga
dynamic monitored colonnaScelta: Colonna

//Per verificare che il magazzino è pieno
derived isMagazzinoPieno: Boolean

//La probabilità la faccio derived o static? Creo un dominio probabilità?
//I valori di probabilità li faccio interi o reali?
static probabilita: Riga -> Probabilita

definitions:
domain Riga = {1 : 5}
domain Colonna = {1 : 5}
domain Probabilita = {1 : 10}

function probabilita($riga in Riga) =
	switch $riga
		case 1 : 1
		case 2 : 2
	    case 3 : 3
		case 4 : 4
		case 5 : 5
	endswitch
	
function isMagazzinoPieno = (forall $riga in Riga, $colonna in Colonna with container($riga,$colonna) = FULL)

rule r_riempiContainer($riga in Riga, $colonna in Colonna) =
	if container($riga, $colonna) = EMPTY then
		container($riga, $colonna) := FULL
	endif
	
/*
Per implementare la casualità dovrei avere una funzione che genera in modo casuale un numero tra 0.0 e 1.0.
Asmeta non supporta nè una comparazione tra reali di questo tipo nè la comparazione di un numero casuale scelto da una choose tra un insieme Integer
ed una funzione con dominio in Integer. Bisogna fare sostanzialmente un domain a parte in cui far ricadere questa comparazione

Ovvero se fai:
	choose $i in {0 : 10} with true do
		if ($i < probabilita($riga)) then
			container($riga, $colonna) := EMPTY
		endif 

La compilazione in SMV non va
*/

rule r_svuotaContainer($riga in Riga, $colonna in Colonna)=
	choose $i in Probabilita with true do
		if ($i < probabilita($riga)) then
			container($riga, $colonna) := EMPTY
		endif 
	
rule r_svuotaMagazzino =
	forall $riga in Riga, $colonna in Colonna with true do
		if container($riga, $colonna) = FULL then
			r_svuotaContainer[$riga, $colonna]
		endif

//CTL
//esiste uno stato in cui tutti i contanier sono occupati;
CTLSPEC(ef(isMagazzinoPieno))
//esiste uno stato a partire dal quale inizia un cammino in cui tutti i container sono occupati
CTLSPEC(ef(eg(isMagazzinoPieno)))

//Trovare tramite model checking un cammino che porti in uno stato in cui i container (1,2) e (1,5) sono occupati.


main rule r_Main =
	par
		r_riempiContainer[rigaScelta,colonnaScelta]
		r_svuotaMagazzino[]
	endpar
	
default init s0:
function container($riga in Riga, $colonna in Colonna) = EMPTY
