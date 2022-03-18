# Solveur DPLL récursif


Implémentation d'un solveur DPLL récursif en OCaml

### Tester le solveur


Outre les exemples de test inclus dans dpll.ml (exemple_3_12,
exemple_7_2, exemple_7_4, exemple_7_8, systeme, coloriage), vous
pouvez utiliser le Makefile en appelant [make]

#TODO: ajouter les fichiers de test

pour compiler un exécutable natif et le tester sur des fichiers au
format DIMACS. Vous trouverez des exemples de fichiers dans le dossiers **/test-files**

https://www.irif.fr/~schmitz/teach/2021_lo5/dimacs/

#TODO : faire affichage : OK ou pas (préciser ?)
Par exemple,

./dpll /test-files/sudoku-4x4.cnf

devrait répondre

SAT
-111 -112 113 -114 -121 -122 -123 124 -131 132 -133 -134 141 -142 -143 -144 -211 212 -213 -214 221 -222 -223 -224 -231 -232 -233 234 -241 -242 243 -244 311 -312 -313 -314 -321 322 -323 -324 -331 -332 333 -334 -341 -342 -343 344 -411 -412 -413 414 -421 -422 423 -424 431 -432 -433 -434 -441 442 -443 -444 0
