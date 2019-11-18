////////////////////////////////////////////////////////////////////
//                                                                //
//                 QUOTIENTS TO FORMS CLASS GROUPS                //
//                     WITH SMALLER CONDUCTOR                     //
//                          David Kohel                           //
//                    Last modified April 2000                    //
//                                                                //
////////////////////////////////////////////////////////////////////

// freeze;

// Intrinsics:
// FundamentalQuotient, QuotientMap

forward QuotientForm, PullbackForm;
 
intrinsic FundamentalQuotient(Q::QuadBin) -> Map
   {The quotient homomorphism from the class group of Q to the
   class group of fundamental discriminant.}   
   Q1 := QuadraticForms(FundamentalDiscriminant(Discriminant(Q)));
   return QuotientMap(Q,Q1);
end intrinsic;

intrinsic QuotientMap(Q2::QuadBin,Q1::QuadBin) -> Map
   {The quotient homomorphism from the class group of Q2 with 
   discriminant D2 to the class group of Q1 with discriminant D1, 
   where D2 = m^2*D1.}
   D2 := Discriminant(Q2);
   D1 := Discriminant(Q1);
   t, m := IsSquare(D2/D1);
   require t : "Forms must have the same fundamental discriminant";
   require Denominator(m) eq 1 : 
      "Conductor of argument 1 must divide that of argument 2";
   m := Numerator(m);
   return map< Q2 -> Q1 | f :-> QuotientForm(f,m) >,
          map< Q1 -> Q2 | g :-> PullbackForm(g,m) >;
end intrinsic;

function QuotientForm(f,m)
   if m eq 1 then
      return Reduction(f);
   end if;
   a, b, c := Explode(Eltseq(f));
   Q1 := QuadraticForms((b^2-4*a*c) div m^2);
   while m mod 2 eq 0 do
      if a mod 2 eq 0 then
         a div:= 4;
         b div:= 2;
         m div:= 2;
      elif c mod 2 eq 0 then
         c div:= 4;
         b div:= 2;
         m div:= 2;
      else 
         c := (a+b+c) div 4;
         b := a + (b div 2);
         m div:= 2;
      end if;   
   end while;
   if m eq 1 then
      return Reduction(Q1![a,b,c]);
   end if;
   m1 := GCD([a,b,m]);
   a div:= m1^2;
   b div:= m1;
   m div:= m1;
   if m eq 1 then
      return Reduction(Q1![a,b,c]);
   end if;
   t := -InverseMod(2*a,m)*b mod m; 
   c := (a*t^2 + b*t + c) div m^2;  
   b := (2*a*t+b) div m;
   return Reduction(Q1![a,b,c]);
end function;

function PullbackForm(f,m)
   a, b, c := Explode(Eltseq(f));
   if GCD(a,m) eq 1 then
      Q2 := QuadraticForms(m^2*(b^2-4*a*c));
      return Reduction(Q2![a,m*b,m^2*c]);
   elif GCD(c,m) eq 1 then
      Q2 := QuadraticForms(m^2*(b^2-4*a*c));
      return Reduction(Q2![c,-m*b,m^2*a]);
   end if;
   m1 := m;
   t1 := GCD(a,m);
   while t1 ne 1 do 
      m1 div:= t1;
      t1 := GCD(a,m1);
   end while;
   m2 := m div m1;
   if m1 ne 1 then
      Q2 := QuadraticForms(m1^2*(b^2-4*a*c));
      return PullbackForm(Reduction(Q2![a,m1*b,m1^2*c]),m2);
   end if;
   m1 := m;
   t1 := GCD(c,m);
   while t1 ne 1 do 
      m1 div:= t1;
      t1 := GCD(c,m1);
   end while;
   m2 := m div m1;
   if m1 ne 1 then
      Q2 := QuadraticForms(m1^2*(b^2-4*a*c));
      return PullbackForm(Reduction(Q2![c,-m1*b,m1^2*a]),m2);
   end if;
   Q2 := QuadraticForms(b^2-4*a*c);
   return PullbackForm(Q2![a+b+c,b+2*c,c],m);
end function;


