asm lottoT

import ../../Library/StandardLibrary
import ../../Library/CTLlibrary

//Esercizio preso dal gruppo telegram, svolgimento non mio ma comunque valido
 
 signature:
 
 domain Numbers subsetof Integer
 domain PlayedNumbers subsetof Integer
 dynamic shared extracted : Numbers -> Boolean
 dynamic controlled playerNumbers: Numbers -> Boolean 
 dynamic controlled numbers : PlayedNumbers
 dynamic controlled numbersExtracted : PlayedNumbers
 dynamic controlled match : PlayedNumbers
 monitored choosenNumber: Numbers 
 //out outMessage : String
 
 definitions:
 
 domain PlayedNumbers = {0:10}
 domain Numbers = {1:90}
 
 rule r_extractAndCheck = 
       choose $i in Numbers with extracted($i) = false do 
       par
       extracted($i):= true
       numbersExtracted := numbersExtracted + 1
       if(playerNumbers($i)) then 
       match := match + 1
       endif
       endpar
       
 /* Commentato perché NuSMV non supporta le stringhe
  * 
  * rule r_win = 
      switch(match)
      case 0: outMessage:="0 EUR"
      case 1: outMessage:="0 EUR"
      case 2: outMessage:="AMBO: 10 EUR"
      case 3: outMessage:="TERNO: 20 EUR"
      case 4: outMessage:="QUATERNA: 30 EUR"
      case 5: outMessage:="CINQUINA: 50 EUR"
      endswitch*/
      
      
      // Se non hai un computer quantico diminuisci a piacere il range del dominio Numbers prima di verificare le CTLSPEC
      // altrimenti si pianta Eclipse
      
      CTLSPEC(ef(match=5))
      CTLSPEC(ef(match=0))
      // questa fallisce, ma serviva soltanto per il controesempio
      CTLSPEC(not(ef(match=3)))
     
 main rule r_Main = 
     if(numbers < 10) then 
     	par
     	playerNumbers(choosenNumber):=true
     	numbers := numbers + 1
     	endpar
     else
     	if(numbersExtracted < 5) then 
     		r_extractAndCheck[]
     	else skip //r_win[]
     	endif
     endif
     

default init s0:
function extracted($i in Numbers)=false
function playerNumbers($i in Numbers)=false
function numbers = 0
function numbersExtracted = 0
function match = 0
