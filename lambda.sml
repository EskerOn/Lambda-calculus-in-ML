(*
Tipos en el calculo lambda
Escalante Hernandez Alejandro
*)
datatype vars = x of int
datatype t = v of vars | l of vars*t | a of t*t

fun elimina(any, [])= []
|   elimina(any, f::r)= if f=any then
                            elimina(any, r)
                            else
                            f::elimina(any, r);

fun fv(v x1)=[x1]
|   fv(a(m,n))=fv(m)@fv(n)
|   fv(l(x1,P))=elimina(x1,fv(P));

fun getvar([]) = 0 
|   getvar([x(i)]) = i+1
|   getvar(x(i)::r) =
      let 
        val y = getvar r
      in
        if i > y then i+1 else y
      end

fun pert(any, nil)= false
|   pert(any, f::r)= if any=f then
                        true
                        else
                        pert(any,r);

fun subs(v x1, y, N) = if x1 = y
                        then N
                        else v x1
|   subs(a(P,Q), y, N) = a(subs(P, y, N), subs(Q, y, N))
|   subs(l(x1, P), y, N) = if x1 = y
                            then l(x1, P)
                            else if pert(x1,fv(N))=false
                                then l(x1,subs(P, y, N))
                                else l(x(getvar(fv(P)@fv(N))),subs(subs(P,x1,v(x(getvar(fv(P)@fv(N))))),y,N));

fun redex(v x1)=false
|   redex(a(l(x1,m),n))=true
|   redex(a(m,n))=redex(m) orelse redex(n)
|   redex(l(x1,m))=redex(m);

fun beta(a(l(x1,M),N)) = subs(M, x1, N)
|   beta(l(x1,M)) = l(x1, beta(M))
|    beta(a(M,N)) = a(beta(M),beta(N))
|    beta(v x1)=v x1;

fun ron(a(l(x1,M),N)) = subs(M, x1, N)
|   ron(a(M,N)) = if redex(M)=true then
                    a(ron(M), N)
                    else
                    a(M, ron(N))
|   ron(l(x1,M)) = l(x1, ron(M))
|   ron(v x1)=v x1;

fun roaid(a(l(x1,M),N)) = if redex(l(x1,M)) = true then
                            a(roaid(l(x1,M)), N)
                          else
                          if redex(N)= true then
                            a(l(x1,M), roaid(N))
                          else
                          subs(M, x1, N)
|   roaid(a(M,N)) = a(roaid(M),roaid(N))
|   roaid(l(x1,M)) = l(x1, roaid(M))
|   roaid(v x1)=v x1;

fun roadi(a(l(x1,M),N)) = if redex(N)= true then
                          a((l(x1,M)), roadi(N))
                          else
                          if redex(l(x1,M)) = true then
                          a(roadi(l(x1,M)), N)
                          else
                          subs(M, x1, N)
|   roadi(a(M,N)) = if redex(N)= true then
                        a(M, roadi(N))
                        else
                        a(roadi(M), N)
|   roadi(l(x1,M)) = l(x1, roadi(M))
|   roadi(v x1)=v x1;

fun ronaster(any)= 
    let
      fun ronasterpa(any, pa, index)= if redex(any)= true then
                              ronasterpa(ron(any), pa@[(index, any)], index+1)
                              else
                              pa@[(index, any)]
    in
        ronasterpa(any, [], 0)
    end;
fun ronasters(any)=if redex(any)=true then
                  ronasters(ron(any))
                  else 
                  any;

fun roaidaster(any)=if redex(any)=true then
                  roaidaster(printVal(roaid(any)))
                  else 
                  any;

fun roadiaster(any)=if redex(any)=true then
                  roadiaster(printVal(roadi(any)))
                  else 
                  any;

fun betaster(any)=if redex(any)=true then
                  betaster(printVal(beta(any)))
                  else 
                  any;

val TrueT = l(x 1,l(x 2, v(x 1)));
val FalseT = l(x 1,l(x 2, v(x 2)));

val zeroT = l(x 8, l(x 7, v(x 7)));

val ite = l(x 3, l(x 1, l(x 2, a(a(v(x 3), v(x 1)),v(x 2)))));

val notT = l(x 3,a(a(v(x 3),FalseT), TrueT));

val andT= l(x 3, l(x 4, a(a(v(x 3),v(x 4)),FalseT)))

val orT = l(x 3, l(x 4, a(a(v(x 3), TrueT), v(x 4))))

val pi = l(x 3, l(x 4, l(x 5, a(a(v(x 5),v(x 3)),v(x 4)))));

val pi1= l(x 6, a(v(x 6), l(x 3, l(x 4, v(x 3)))));

val pi2= l(x 6, a(v(x 6), l(x 3, l(x 4, v(x 4)))));

val suc = l(x 3, l(x 8, l(x 7, a(a(v(x 3), v(x 8)),a(v(x 8), v(x 7))))));

val plus = l(x 3, l(x 4, a(a(v(x 3), suc),v(x 4))));

val mul = l(x 3, l(x 4, a(a(v(x 3),a(plus, v(x 4)) ),zeroT)));

val exp= l(x 3, l(x 4, a(v(x 4), v(x 3))));

val nul = l(x 1, l(x 2, v(x 2)));

val cons=l(x 3, l(x 4, l(x 7, a(a(v(x 7), v(x 3)), v(x 4)))));

val head = l(x 3, a(v(x 3),l(x 3, l(x 4, v(x 3)))));

val tail = l(x 3, a(v(x 3),l(x 3, l(x 4, v(x 4)))));

val Y = l(x 10, a(l(x 11, a(v(x 10),a(v(x 11),v(x 11)))),l(x 11, a(v(x 10),a(v(x 11),v(x 11))))));

val pred = l(x 3, l(x 8, l(x 7, a(a(a(v(x 3), l(x 4, l(x 5, a(v(x 5), a(v(x 4), v(x 8)))))), l(x 6, v(x 7))),l(x 6, v(x 6))))));

val isz = l(x 3, a(a(v(x 3), l(x 3, FalseT)),TrueT));

val suma = a(Y, l(x 9, l(x 3, l(x 4, a(a(a(ite,a(isz, v(x 3))),zeroT),a(a(plus, a(a(v(x 9),a(pred, v(x 3))),v(x 4))), a(suc, zeroT)))))));

val prod = a(Y, l(x 9, l(x 3, l(x 4, a(a(a(ite,a(isz, v(x 3))),zeroT),a(a(plus, a(a(v(x 9),a(pred, v(x 3))),v(x 4))), v(x 3)))))));

val fact = a(Y, l(x 9, l(x 3, a(a(a(ite,a(isz, v(x 3))),a(suc, zeroT)),a(a(mul, a(v(x 9), a(pred,v(x 3)))),v(x 3))))));

val suma2 = a(Y, l(x 9, l(x 3, l(x 4, a(a(a(ite,a(isz, v(x 3))),v(x 4)),a(a(plus, a(a(v(x 9),a(pred, v(x 3))),v(x 4))), a(suc, zeroT)))))));

val prod2 = a(Y, l(x 9, l(x 3, l(x 4, a(a(a(ite,a(isz, v(x 3))),zeroT),a(a(plus, a(a(v(x 9),a(pred, v(x 3))),v(x 4))), v(x 4)))))));