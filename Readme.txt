Introduction: 
This prototype, which is used to compute the result R of forgetting some set V of atoms from a give CTL formula F (in the "Filename" below), is implemented in Prolog.   
 

 How to run this prototype?

 If you want to compute forgetting results, you to input a set V of atoms and a formula F after opening the source code with SWI-prolog.
 Besides, the atoms appearing in F should be transformed into a proposition using predicts ``gain\_prop/2" and ``add\_propTerm/1".
Once we added the atoms in F to propositions, we can use ``kForget(F, V, R)" to obtain the result R of forgetting V from F. 

 If you want to compute SNC, you should prepare a ``.txt" file (e.g. snc.txt)  that contains an S5 formula F, an atom Q, and a set of atoms P to compute the SNC of Q on P under F. 
Use SWI-prolog to open the program, enter ``ksnc", then enter the txt file name according to the prompt, and the result is saved in the file ``Cresult.txt".
