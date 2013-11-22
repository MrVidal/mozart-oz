/*-------------------------------------------------------------------------------------------------------------------
x0 + : : : + xn-1 = n y (-1)x0 + : : : + (n-2)  xn-1 = 0
Son Restricciones redundantes porque con el solo hecho de plantear la restriccion  {FD.exactly A.(I+1) A I}, se esta garantizando que
la serie sea correcta (restriccion de que almenos o exactamente existan K campos de la tupla S iguales a I),entonces las restricciones
x0 + : : : + xn-1 = n y (-1)x0 + : : : + (n - 2)  xn-1 = 0, solo ayudan a reducir el tamaño del arbolde busqueda y asi optimizar de
cierta forma el algoritmo.
-----------------------------------------------------------------------------------------------------*/
declare
fun {SolSecuencia N Lst}  
   proc{$ A}
      {FD.tuple mSeq N 0#N-1 A}
      {For 0 N-1 1
        %restriccion de que almenos o exactamente existan K campos de la tupla S iguales a I
        %I  = 0 | 1 | 2 | 3
        %K =1 | 2 | 1 | 0
       proc {$ I}
	  {FD.exactly A.(I+1) A I}
       end
      }
      %restricciones redundantes
      %toda serie magica la suma de sus es Xi=N
      {FD.sumC Lst A '=:' 0}%hace producto punto entre Lst y A
      {FD.sum A '=:' N}    
      {FD.distribute ff A}
   end  
end
fun{Secuencia N}
   if {IsNumber N} then
      Lst = {List.number ~1 N-2 1}
   in
      {SearchOne {SolSecuencia N Lst}}.1
   else 'Error en tipo de dato'
   end
end
{Browse {Secuencia 5}}
