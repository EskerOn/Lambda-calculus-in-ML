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

val zeroT = l(x 1, l(x 2, v(x 2)));

fun ite(b,x1,x2) = a(a(b, x1), x2);

fun notT(b) = a(a(b, FalseT), TrueT);

fun andT(x1, x2) = a(a(x1,x2), FalseT);

fun orT(x1, x2) = a(a(x1,TrueT), x2);

fun pi(le,r, z) = l(z ,a(a(v(z),le),r));

fun pi1(u)= a(u, TrueT);

fun pi2(u)= a(u, FalseT);

fun suc(x1, s, z)= l(x 1, l(x 2 ,a(s, a(a(x1,s), z))));

fun plus(x1, x2)= l(x 1,l(x 2, a(a(x1, v(x 1)), a(x2,a(v(x 1), v(x 2))))));

fun mul(x1, x2)= l(x 1, a(x1, a(x2, v(x 1))));

fun exp(x1, x2)= a(x2, x1);

val nul = l(x 1, l(x 2, v(x 2)));

fun cons(h, t) = l(x 2, a(v(x 2), a(h, t)));

fun head(li)= a(li, l(x 1, l(x 2, v(x 1))));

fun tail(li)= a(li, l(x 1, l(x 2, v(x 2))));