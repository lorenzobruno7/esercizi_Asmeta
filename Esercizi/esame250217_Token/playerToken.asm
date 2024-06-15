asm playerToken

import ../../Library/StandardLibrary
import ../../Library/CTLlibrary

/*
 ----Modello AsmetaL - 25 maggio 2017----
---Esame riuscito in data 31 maggio 2024 (Con 4 Player)---
Tre giocatori attorno ad un tavolo. Inizialmente ogni giocatore ha 3 token. Di seguito la rappresentazione grafica:

******************************* 	
* 	Player2 ------- Player3	  *
* 		-				-     *
* 		 -			   -      *
*		  -		      -	      *
* 		   -        -         *
* 			Player1			  *
*******************************

Ad ogni passo di simulazione, la macchina sceglie un giocatore a caso che esegue una delle seguenti mosse:
	1. se ha almeno un token, ne mette uno nel piatto;
	2. se non ha alcun token:
		a) se il suo vicino a destra ha almeno un token, ne prende uno (ma non usa a quel giro);
		b) se il suo vicino a destra non ha alcun token, controlla il vicino a sinistra: se questo ha almeno un token, ne passa uno al suo vicino di destra.

Invarianti
Scrivere un invariante del modello per garantire che la somma dei token dei giocatori e del piatto `e sempre uguale a 9

CTL:
• nel sistema ci sono sempre al massimo 9 token;
• ogni giocatore non ha mai più di 3 token;
• prima o poi nessun giocatore ha token;
• prima o poi il piatto ha 9 token.
*/

signature:
//Entità di gioco che manipolo
abstract domain Player
domain Token subsetof Integer

//Una variabile che, dato un player, da il numero di token e una variabile che rappresenta il plate
dynamic controlled numToken: Player -> Token
dynamic controlled plate: Token
//Due variabili che dato un player ci danno i player a sinistra e a destra
dynamic controlled left: Player -> Player
dynamic controlled right: Player -> Player

//Una variabile sulla quale definire una invariante riguardo il numero totale di token presenti in ogni iterazione
derived totalTokens: Token 

//Definiamo i tre player che avremo nel programma
static player1: Player
static player2: Player
static player3: Player

definitions:
//Inizializzazioni statiche
domain Token = {0 : 9}

function totalTokens = numToken(player1) + numToken(player2) + numToken(player3) + plate

rule r_giveToPlaye($player in Player) =
par
	numToken($player) := numToken($player) - 1
	plate := plate + 1
endpar

rule r_giveToPlayer($currentPlayer in Player, $fromPlayer in Player) = 
par
	numToken($fromPlayer) := numToken($fromPlayer) - 1
	numToken($currentPlayer) := numToken($currentPlayer) + 1
endpar

//Devo mettere una variabile hasToken o posso fare così la verifica?
rule r_PlayerMove($player in Player)=
if(numToken($player) > 0) then
	r_giveToPlate[$player]
else if (numToken(right($player)) > 0) then
	r_giveToPlayer[$player, right($player)]
else if (numToken(left($player)) > 0) then
	r_giveToPlayer[left($player), right($player)]
endif endif endif

// CTL
CTLSPEC(ag(totalTokens < 10))
CTLSPEC(ag(numToken(player1) <= 3 and numToken(player2) <= 3 and numToken(player3) <= 3))
CTLSPEC(ag(ef(numToken(player1) = 0 and numToken(player2) = 0 and numToken(player3) = 0)))
CTLSPEC(ag(ef(plate = 9)))

// INVARIANTI
invariant over numToken, plate : totalTokens = 9

main rule r_Main =
choose $player in Player with true do
r_PlayerMove[$player]

//Devo mettere un currentPlayer?


default init s0:
function plate = 0
function numToken($player in Player) = 3

function left($player in Player) =
switch $player
	case player1 : player2
	case player2: player3
	case player3: player1
endswitch

function right($player in Player) =
switch $player
	case player1 : player3
	case player2: player1
	case player3: player2
endswitch 
