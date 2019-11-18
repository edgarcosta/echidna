freeze;
intrinsic RationalFunctionInversion(f::FldFunRatUElt,
   g::FldFunRatUElt) -> FldFunRatMElt
   {For f, g rational functions in t compute a polynomial over 
   the rational function field h(x, y) such that h( f, g ) = t.}

   require Parent(f) eq Parent(g)
     : "Rational functions defined in different fields";
   
   kf := Parent(f);
   kft := PolynomialRing(kf);
   
   m := hom< kf -> kft | kft.1 >;
   hf := m(Numerator(f)) - m(Denominator(f))*kf.1;
   hg := m(Numerator(g)) - m(Denominator(g))*kf.1;
   
   require (Degree(hf) eq 0 and Degree(hg) eq 1) or 
           (Degree(hg) eq 0 and Degree(hf) eq 1) or
           (Degree(hf) gt 0 and Degree(hg) gt 0)
     : "Rational inversion is not possible";
   
   if Degree(hf) eq 1 then
      h := -Coefficient(hf, 0) / Coefficient(hf, 1);
      h := kft!h;
      switched := false;
   elif Degree(hg) eq 1 then
      h := -Coefficient(hg, 0) / Coefficient(hg, 1);
      h := kft!h;
      switched := true;
   else
      
      if Degree(hf) gt Degree(hg) then
         hh := hf;
         hf := hg;
         hg := hh;
         gg := f;
         switched := true;
      else
         gg := g;
         switched := false;
      end if;
      
      F := FunctionField(hf: Check := false);
      m := hom< kf -> F | F.1 >;
      gg := m(gg);
   
      M := [ ElementToSequence(gg^i) : i in [0..Degree(F)-1] ];
      M := Matrix(Degree(F), &cat M);
   
      require Determinant(M) ne 0
        : "Rational inversion is not possible";
      
      M := M^-1;
      v := M[2];
      
      h := &+ [ v[i]*kft.1^(i-1) : i in [1..Degree(F)] ];
      
   end if;
      
   kfg := RationalFunctionField(kf, 2);
   h := &+ [ Evaluate(Coefficient(h, i), kfg.1)*kfg.2^i 
             : i in [0..Degree(h)] ];
   
   if switched then
      h := hom< kfg -> kfg | [ kfg.2, kfg.1 ] >(h);
   end if;         
         
   require Evaluate(Evaluate(h, 1, f), 2, g) - kf.1 eq 0
     : "Error in computation";
   
   return h;
   
end intrinsic;

