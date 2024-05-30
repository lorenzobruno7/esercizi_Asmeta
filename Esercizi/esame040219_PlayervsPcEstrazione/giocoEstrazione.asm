asm giocoEstrazione

import ../../Library/StandardLibrary
import ../../Library/CTLlibrary

/*
Requisiti

L’utente gioca contro il PC.
Ogni giocatore ha la possibilità di estrarre un numero da 1 a 5.
Ad ogni estrazione, vince chi ha estratto il numero di valore maggiore, mentre se estraggono lo stesso numero non vince/perde nessuno.

Ogni giocatore ha inizialmente 5 euro a disposizione. Se perde, dal suo credito viene scalato 1e e viene aggiunto
all’avversario. Se estraggono lo stesso numero non viene scalato denaro a nessuno.
Il gioco continua finché uno dei due giocatori arriva a 0e.

Modello AsmetaL-
Ad ogni passo di simulazione, il pc e l’utente estraggono un numero. Si possono verificare le seguenti condizioni:
• Il numero dell’utente è uguale a quello estratto dal pc: partita patta; nessuno perde/guadagna denaro.
• Il numero dell’utente supera quello estratto dal pc: vince l’utente; l’utente guadagna 1e, il pc perde 1e.
• Il numero dell’utente è minore di quello estratto dal pc: vince il pc; l’utente perde 1e, il pc guadagna 1e.

Inizialmente entrambi hanno un credito di 5e ed il gioco continua finché uno dei due giocatori raggiunge 0e.
Quando il gioco termina, si vuole sapere il vincitore (WINUSER — WINPC — PATTA) utilizzando un’opportuna funzione. (tramite variabile)
Utilizzare funzioni derived per winner e finalWinner,  definite, come locazioni per memorizzare il risultato parziale del gioco e quello totale.

Invarianti
Scrivere un invariante del modello per garantire che la somma dei crediti dei due giocatori `e sempre uguale a 10.

Specificare i seguenti due scenari:
• Se il giocatore seleziona il numero 4 ed il pc sorteggia 2, allora l’utente vince 1 euro.
• Se il giocatore sorteggia 4 ed il pc sorteggia 5, allora l’utente perde 1 euro ed il pc vince 1 euro.

CTL
Specificare e verificare tramite AsmetaSMV le seguenti propriet`a CTL:
• il saldo dell’utente pu`o assumere un qualsiasi valore nell’intervallo [0, 10];
• nel sistema ci sono sempre 10e;
• esiste un cammino in cui il saldo del pc ´e sempre maggiore o uguale a 1e.


ATTENZIONE: NON VIENE DETTO CHE IL NUMERO VIENE SCELTO CASUALMENTE QUINDI NELLA SIMULAZIONE VIENE INSERITO IL VALORE

*/

signature:
//Definiamo le "entità" del nostro modello
enum domain Player = {USER | PC}
enum domain Winner = {WINUSER | WINPC | PATTA}
//Domini per l'estrazione del numero e per i soldi
domain Estrazione subsetof Integer
domain Soldi subsetof Integer

//Funzione che rappresenta saldo due giocatori, la giocata e il vincitore
dynamic controlled saldo: Player -> Soldi
dynamic monitored giocata: Player -> Estrazione
dynamic out vincitore: Winner

derived winner: Prod(Estrazione, Estrazione) -> Winner 
derived finalWinner: Winner

definitions:
//Definiamo il dominio dei numeri estraibili
domain Estrazione = {0 : 5}
//Definiamo il dominio dei soldi che una entità può possedere, 0 fino ad un massimo di 10
domain Soldi = {0 : 10}

function winner($estrazionePlayer in Estrazione, $estrazionePC in Estrazione) =
	if ($estrazionePlayer > $estrazionePC) then WINUSER
	else if ($estrazionePC > $estrazionePlayer) then WINPC
	else PATTA
	endif endif

function finalWinner =
	if ( saldo(USER) = 0 and saldo(PC) != 0 ) then WINPC
	else if ( saldo(USER) != 0 and saldo(PC) = 0 ) then WINUSER
	else PATTA
	endif endif
	
rule r_GiocaTurno = 
	switch(winner(giocata(USER),giocata(PC)))
		case WINUSER:
			par
				saldo(PC) := saldo(PC) - 1
				saldo(USER) := saldo(USER) + 1
			endpar
		case WINPC:
			par
				saldo(PC) := saldo(PC) + 1
				saldo(USER) := saldo(USER) - 1
			endpar
	endswitch
		
//CTL

//il saldo dell’utente può assumere un qualsiasi valore nell’intervallo[0, 10] Euro
CTLSPEC(ef(saldo(USER) = 0) or
	saldo(USER) = 1 or
	saldo(USER) = 2 or
	saldo(USER) = 3 or
	saldo(USER) = 4 or
	saldo(USER) = 5 or
	saldo(USER) = 6 or
	saldo(USER) = 7 or
	saldo(USER) = 8 or
	saldo(USER) = 9 or
	saldo(USER) = 10)
	
//nel sistema ci sono sempre 10 Euro;
CTLSPEC(ag(saldo(PC) + saldo(USER) = 10))
//esiste un cammino in cui il saldo del pc è sempre maggiore o uguale a 1 Euro.
CTLSPEC(ef(saldo(PC) >= 1))


//Invarianti
invariant over saldo: saldo(USER) + saldo(PC) = 10

main rule r_Main =
	if (finalWinner != PATTA) then
		vincitore := finalWinner
	else 
		r_GiocaTurno[]
	endif
	

default init s0:
//All'inizio USER e PC hanno nel loro saldo 5 euro ciascuno
function saldo($p in Player) = 5
