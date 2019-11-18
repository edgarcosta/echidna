freeze;
////////////////////////////////////////////////////////////////////
//                                                                //  
//                      BINARY THETA SERIES                       //
//                 FOR MODULAR FORMS AND FUNCTIONS                //
//                          David Kohel                           // 
//                                                                // 
////////////////////////////////////////////////////////////////////

forward CoprimeCoefficients;

intrinsic BinaryThetaSequence(D::RngIntElt : Precision := 100) 
   -> SeqEnum {}
   require D mod 4 in {0,1} :
      "Argument must be congruent to 0 or 1 mod 4";
   require D lt 0 : "Argument must be negative";
   A, m := ClassGroup(BinaryQuadraticForms(D));
   S := [ Representative(C) : C in { {x,-x} : x in A } ];
   PS := LaurentSeriesRing(RationalField());
   return [ PS | ThetaSeries(m(x),Precision) : x in S ];
end intrinsic;

intrinsic TwistedBinaryThetaSequence(
   D::RngIntElt, m::RngIntElt, s::RngIntElt 
      : Precision := 100) -> SeqEnum 
   {}
   s := s mod m;
   require D mod 4 in {0,1} :
      "Argument must be congruent to 0 or 1 mod 4";
   require D lt 0 : "Argument 1 must be negative";
   if m in {2,3} then
      require &and[ KroneckerSymbol(D,p) eq -1 : p in PrimeDivisors(m) ] : 
         "Prime divisors of argument 2 must be inert in argument 1.";
   end if;
   A, h := ClassGroup(BinaryQuadraticForms(D));
   S := [ Representative(C) : 
           C in { {x,-x} : x in A | f[1] mod m eq s 
             or f[3] mod m eq s where f := h(x) } ];
   print "Forms =", [ h(x) : x in S ];
   PS := LaurentSeriesRing(RationalField());
   return [ PS | TwistedThetaSeries( h(x), m 
                 : Precision := Precision) : x in S ];
end intrinsic;

intrinsic ThetaSeries(f::QuadBinElt, eps::GrpDrchElt 
   : Precision := 100) -> SeqEnum 
   {}
   Q := Parent(f);
   K := Codomain(eps);
   m := Conductor(eps);
   a, b, c := Explode(Eltseq(Reduction(f))); 
   if Evaluate(eps,Conductor(Q)) eq 0 then
      if GCD(a,m) eq 1 then
         a0 := 2*a mod m;
         b0 := b mod m;
      end if;
   end if;
   PS := PowerSeriesRing(K); q := PS.1;
   prec := Precision;
   n1 := Ceiling(Sqrt(prec/a));
   n2 := Ceiling(Sqrt(prec/c));
   print "n1 =", n1;
   print "n2 =", n2;
   return &+[ &+[ // Evaluate(eps,a0*x+b0*y) * 
                     q^((a*x+b*y)*x+c*y^2) 
                        : x in [-n1..n1] ] 
                           : y in [-n2..n2] ] + O(q^(prec+1));   
end intrinsic;

intrinsic TwistedThetaSeries(
   f::QuadBinElt : Precision := 100) -> SeqEnum {}
   Q := Parent(f);
   a, b, c := Explode(Eltseq(f)); 
   if c mod 2 eq 0 then
      c +:= a + b; 
      b +:= 2*a;
   elif a mod 2 eq 0 then
      a +:= b + c; 
      b +:= 2*c;
   end if;
   Q2 := BinaryQuadraticForms(4*Discriminant(f)); 
   PS := LaurentSeriesRing(RationalField());
   return PS ! ( ThetaSeries(Q2![a,2*b,4*c],Precision) -
                 ThetaSeries(Q2![4*a,2*b,c],Precision) )/2; 
end intrinsic;

intrinsic TwistedThetaSeries(
   f::QuadBinElt, m::RngIntElt : Precision := 100) -> SeqEnum {}
   Q := Parent(f);
   a, b, c := Explode(Eltseq(f)); 
   require m in {2,3,4} : "Argument 2 must be 2, 3, or 4"; 
   PS := LaurentSeriesRing(RationalField());
   if m eq 2 then
      // Discriminant should be inert or split
      q := PS.1;
      prec := Precision;
      t := ThetaSeries(f,prec);
      return (&+[ KroneckerSymbol(-4,n)*Coefficient(t,n)*q^n
                : n in [1..prec by 2] ])/2 + O(q^(prec+1));
   elif m eq 3 then
      // Discriminant should be inert.
      Q2 := BinaryQuadraticForms(m^4*Discriminant(f)); 
      return PS ! ( ThetaSeries(Q2![a,9*b,81*c],Precision) -
         ThetaSeries(Q2![a+3*b+9*c,9*b+54*c,81*c],Precision) ) / 2; 
   elif m eq 4 then
      // Discriminant should be ramified.
      a, b, c := CoprimeCoefficients(a,b,c,m);
printf "[a,b,c] = [%o,%o,%o]\n", a, b, c;
      Q2 := BinaryQuadraticForms(m*Discriminant(f)); 
      return PS ! ( ThetaSeries(Q2![a,2*b,4*c],Precision) -
                    ThetaSeries(Q2![4*a,2*b,c],Precision) ) / 2; 
   end if;
end intrinsic;

function CoprimeCoefficients(a,b,c,m)
   if GCD(a,m) eq 1 and GCD(c,m) eq 1 then
      return a, b, c;
   end if;
   if m eq 3 then
      if c mod 3 eq 0 then
         c +:= a + b; 
         b +:= 2*a;
      elif a mod 3 eq 0 then
         a +:= b + c; 
         b +:= 2*c;
      end if;
      return a, b, c;
   elif m eq 4 then
      if c mod 2 eq 0 then
         c +:= a + b; 
         b +:= 2*a;
      elif a mod 2 eq 0 then
         a +:= b + c; 
         b +:= 2*c;
      end if;
   end if;
   return a, b, c;
end function;

