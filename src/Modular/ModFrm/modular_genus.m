/* David R. Kohel, 1 December, 2005 */ 

intrinsic ModularGenusX(N::RngIntElt) -> RngIntElt
   {}
   if N eq 1 then
       return 0;
   elif N eq 2 then // (mu_N = 6 not 3)
       return 0;
   end if;
   mu_N := N^3*&*[ Rationals() | 1-1/p^2 : p in PrimeDivisors(N) ]/2;
   return 1 + Integers()!((N-6)*mu_N/(12*N)); 
end intrinsic;

/****-*-magma-*-************************************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
 ***************************************************************************/


/*
  EXPORTS:
    DimensionCuspForms
    DimensionCuspFormsGamma0
    DimensionCuspFormsGamma1
    DimensionNewCuspFormsGamm0
    DimensionNewCuspFormsGamm1

  USES:
    Nothing else from the modular symbols package
*/


/*****************************************************************
  STANDARD MODULAR FORMS DIMENSION FORMULAS

  The first part of this file contains standard functions for
  computing dimensions of spaces of modular forms. It is based 
  on a PARI script, which was written by Bruce Caskel and 
  extended by Kevin Buzzard.
 *****************************************************************/

forward g0, g1;

/*
Faster version in atkin-lehner_genera.m

intrinsic ModularGenusX0(N::RngIntElt) -> RngIntElt
   {}
   return g0(N); 
end intrinsic;
*/

intrinsic ModularGenusX1(N::RngIntElt) -> RngIntElt
   {}
   return g1(N); 
end intrinsic;

function mu0(n)
   return &*([n] cat [1+1/t[1]:  t in Factorization(n)]);
end function;

function mu20(n)
   if n mod 4 eq 0 then
      return 0;
   end if;
   return &*[Integers()| 1+KroneckerSymbol(-4,t[1]): t in Factorization(n)];
end function;

function mu30(n)
   if (n mod 2 eq 0) or (n mod 9 eq 0) then
      return 0 ;
   end if;
   return &*[Integers()| 1+KroneckerSymbol(-3,t[1]): t in Factorization(n)];
end function;

function c0(n) 
   return &+[EulerPhi(Gcd(d, Integers()!(n/d))) : d in Divisors(n)];
end function;

function g0(n)
   return Integers()!(1+mu0(n)/12-mu20(n)/4-mu30(n)/3-c0(n)/2);
end function;

function mu1(n)
   if n le 2 then
      return mu0(n);
   else
      return Integers()!(EulerPhi(n)*mu0(n)/2);
   end if;
end function;

function mu21(n)
   if n lt 4 then return mu20(n); else return 0; end if;
end function;


function mu31(n)
   if n lt 4 then return mu30(n); else return 0; end if;
end function;


function c1(n)
   if n le 3 then return c0(n); end if;
   if n eq 4 then return 3; end if;
   return Integers()!
     (&+[EulerPhi(d)*EulerPhi(Integers()!(n/d))/2 : d in Divisors(n)]);
end function;


function g1(n)
   return Integers()!(1+mu1(n)/12-mu21(n)/4-mu31(n)/3-c1(n)/2);
end function;


function ss0(n,p) 
   assert IsPrime(p) and (n mod p ne 0);
   return g0(n*p) - 2*g0(n) + 1;
end function;

      
function muXNp(n,p) 
   return mu1(n)*mu0(p);
end function;


function mu2XNp(n,p)
   return 0;
end function;


function mu3XNp(n,p)
   return 0;
end function;


function cXNp(n,p) 
   return 2*c1(n);
end function;


function gXNp(n,p)
   if n lt 4 then 
      return g0(n*p);
   end if;
   return 1 + muXNp(n,p)/12 - mu2XNp(n,p)/4 
              - mu3XNp(n,p)/3 - cXNp(n,p)/2 ;
end function;


function ss1(n,p)
   assert IsPrime(p) and (n mod p ne 0);
   return gXNp(n,p) - 2*g1(n) + 1;
end function;


function eisen(p)
   assert IsPrime(p);
   return Numerator((p-1)/12);
end function;


function S0(n,k)
   assert n gt 0;
   if (k le 0) or (k mod 2 ne 0) then 
      return 0;
   end if;
   if k eq 2 then
      return g0(n);
   end if;
   return Integers()!((k-1)*(g0(n)-1) + 
       (k/2-1)*c0(n)+mu20(n)*Floor(k/4)+mu30(n)*Floor(k/3));
end function;


function S1(n,k)
   assert n gt 0;
   if (k le 0) or ((n lt 3) and (k mod 2 ne 0)) then 
      return 0;
   end if;
   if k eq 1 then 
      error "S1, k = 1 not programmed.";
   end if;
   if k eq 2 then
      return g1(n);
   end if;
   if n lt 3 then
      return S0(n,k);
   end if;
   a := (k-1)*(g1(n)-1)+(k/2-1)*c1(n);
   if n eq 4 and k mod 2 ne 0 then
      a +:= 1/2;
   elif n eq 3 then
      a +:= Floor(k/3);
   end if;
   return Integers()!a;
end function;


function idxG0(n)
   return 
      &*[Integers()| t[1]^t[2] + t[1]^(t[2]-1) : t in Factorization(n)];
end function;
   

function idxG1(n)
   return EulerPhi(n)*idxG0(n);
end function;



/*****************************************************************

   Formula of Cohen-Oesterle for dim S_k(Gamma_1(N),eps).
   REF: Springer Lecture notes in math, volume 627, pages 69--78.

 *****************************************************************/

function CohenOesterle(eps, k)
   N    := Modulus(eps);   
   facN := Factorization(N); 
   f    := Conductor(eps); 
   facf := [<p,Valuation(f,p)> : p in [q[1] : q in facN]];
   
   gamma_k := 0;
   if k mod 4 eq 2 then
      gamma_k := -1/4;
   elif k mod 4 eq 0 then
      gamma_k := 1/4;
   end if;
   mu_k := 0;
   if k mod 3 eq 2 then
      mu_k := -1/3;
   elif k mod 3 eq 0 then
      mu_k := 1/3;
   end if;

   function lambda(r,s,p)
     if 2*s le r then
         if IsEven(r) then
            return p^(r div 2) + p^((r div 2)-1);
         else
            return 2*p^((r-1) div 2);
         end if;
      else
         return 2*p^(r-s);
      end if;
   end function;

   K := BaseRing(eps);

   return
     -(1/2)  *  &*[lambda(facN[i][2],facf[i][2],facN[i][1]) 
                  : i in [1..#facN]]
     +gamma_k * &+[K|Evaluate(eps,x) : x in Integers(N) | x^2+1 eq 0]
     +mu_k    * &+[K|Evaluate(eps,x) : x in Integers(N) | x^2+x+1 eq 0];

end function;


function mumu(N)
   if Type(N) ne RngIntElt or N lt 1 then
      error "mumu(N): N must be a positive integer.";
   end if;
   p := 1;
   m := Factorization(N);
   for m in Factorization(N) do
      if m[2] gt 2 then 
         p := 0 ;
      elif m[2] eq 1 then
         p := -2*p;
      end if;
   end for;
   return p;
end function;


////////////////////// END dims.m ////////////////////////////
