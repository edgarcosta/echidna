freeze;
////////////////////////////////////////////////////////////////////
//                                                                //
//                   MODULAR DISCRETE LOGARITHMS                  //
//                        By David Kohel                          //
//                          April 2000                            //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic Modlog(b::RngIntElt,a::RngIntElt,m::RngIntElt) -> RngIntElt
   {The modular logarithm n of a = b^n mod m, or -1 if no n exists;
   modulus m must be a prime power.}
   /* 
   The prime power condition can be dropped, but then a generalized 
   CRT must be used at the end, with checks for failure.  
   */
   yes, p, e := IsPrimePower(m);   
   require yes : "Argument 3 must be a prime power";
   require b mod p ne 0 : "Argument 1 must be coprime to argument 3";
   require a mod p ne 0 : "Argument 2 must be coprime to argument 3";
   if p eq 2 then
      if e eq 1 then
         return 0;
      elif e eq 2 then
         if (a mod 4) eq (b mod 4) then
   	    return 1; 
         else
   	    return -1; 
         end if;
      elif (a mod 8 ne 1) and 
         ((a*InverseMod(b,8) mod 8) mod m) ne 1 then
         return -1; 
      end if;
   end if;
   a0 := GF(p)!a;
   b0 := GF(p)!b;
   n0 := Log(b0,a0);
   if n0 eq -1 then 
      return -1;
   end if;
   a1 := Modexp(a,p-1,p^e);
   b1 := Modexp(b,p-1,p^e);
   if b1 eq 1 then
      if a1 eq 1 then
         return n0;
      end if;
      return -1;
   end if;
   r := 1;
   d := 0;
   n1 := 0; 
   while r+d lt e do
      br := Modexp(b1,p^(r-1),p^(r+d+1));
      cr := a1*Modexp(b1,-n1,p^(r+d+1)) mod p^(r+d+1);
      // assert (cr-1) mod p^(r+d) eq 0;
      sr := (br-1) div p^(r+d);         
      tr := (cr-1) div p^(r+d);         
      while sr eq 0 do
         if tr eq 0 then
       	    d +:= 1; 
            br := Modexp(b1,p^(r-1),p^(r+d+1));
            cr := a1*Modexp(b1,-n1,p^(r+d+1)) mod p^(r+d+1);
            sr := (br-1) div p^(r+d);         
            tr := (cr-1) div p^(r+d);         
         else 
            return -1; 
         end if;
      end while;
      nr := tr*InverseMod(sr,p) mod p;
      n1 +:= p^(r-1)*nr;
      r +:= 1;
   end while;
   return CRT([n0,n1],[p-1,p^(e-2+(p mod 2))]);
end intrinsic;

/* 
This version uses the p-adic logarithm, since it was there!

It appears to be asymptotically much faster, but slightly 
slower for small exponents.
*/

intrinsic Modlog2(b::RngIntElt,a::RngIntElt,m::RngIntElt) -> RngIntElt
   {The modular logarithm n of a = b^n mod m, or -1 if no n exists;
   modulus m must be a prime power.}
   /* 
   The prime power condition can be dropped, but then a generalized 
   CRT must be used at the end, with checks for failure.  
   */
   yes, p, e := IsPrimePower(m);   
   require yes : "Argument 3 must be a prime power";
   require b mod p ne 0 : "Argument 1 must be coprime to argument 3";
   require a mod p ne 0 : "Argument 2 must be coprime to argument 3";
   if p eq 2 then
      if e eq 1 then
         return 0;
      elif e eq 2 then
         if (a mod 4) eq (b mod 4) then
   	    return 1; 
         else
   	    return -1; 
         end if;
      elif (a mod 8 ne 1) and 
         ((a*InverseMod(b,8) mod 8) mod m) ne 1 then
         return -1; 
      end if;
   end if;
   a0 := GF(p)!a;
   b0 := GF(p)!b;
   n0 := Log(b0,a0);
   if n0 eq -1 then 
      return -1;
   elif e eq 1 then
      return n0;
   end if;
   a1 := Modexp(a,p-1,p^e);
   b1 := Modexp(b,p-1,p^e);
   if b1 eq 1 then
      if a1 eq 1 then
         return n0;
      end if;
      return -1;
   end if;
   R := pAdicRing(p,e);
   loga1 := Log(R!a1);
   logb1 := Log(R!b1);
   if Valuation(logb1) gt 1 then
      t := Valuation(logb1);
      R := pAdicRing(p,e+t-1);
      loga1 := Log(R!a1);
      logb1 := Log(R!b1);
   end if;
   n1 := Integers()!(loga1/logb1) mod (p^(e-1));
   return CRT([n0,n1],[p-1,p^(e-2+(p mod 2))]);
end intrinsic;


