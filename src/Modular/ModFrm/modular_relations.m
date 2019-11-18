freeze;
////////////////////////////////////////////////////////////////////
//                                                                //  
//                      BASES AND RELATIONS                       //
//                 FOR MODULAR FORMS AND FUNCTIONS                //
//                          David Kohel                           // 
//                        September 2000                          //
//                                                                // 
////////////////////////////////////////////////////////////////////

// forward ScalingForm;

intrinsic ModularFormsBasis(M::ModBrdt,k::RngIntElt,s::RngIntElt : 
      UseEisenstein := false, Precision := 100) -> SeqEnum
   {The echelonized sequence of modular forms of prime level p, 
   weight k, and sign s under the Atkin-Lehner operator (zero 
   implies the full space).}

   p := Level(M);
   require IsPrime(p) : "Level of argument 1 must be prime";
   // require p mod 12 eq 11 : "Argument 1 must be congruent to 11 mod 12.";
   require k in {0,2} : "Argument 2 must be 0 or 2.";
   require s in {-1,0,1} : "Argument 3 must be 1 or -1.";
   prec := Precision;
   M := BrandtModule(BrandtModuleDatabase(),p,1);
   n := Dimension(M);
   Eis := Matrix(n,1,[ 1 : k in [1..n] ]); 
   Wp := AtkinLehnerOperator(M,p);
   if s eq 0 then 
      if UseEisenstein then 
         B := Basis(M); 
      else
         B := [ M!Eltseq(v) : v in Basis(Kernel(Eis)) ];
      end if; 
   elif UseEisenstein then
      B := [ M!Eltseq(v) : v in 
             Basis( Kernel(Wp + s*(-1)^(k div 2))) ];
   else 
      B := [ M!Eltseq(v) : v in 
             Basis( Kernel(Wp + s*(-1)^(k div 2)) meet Kernel(Eis) ) ];
   end if;
   F := qExpansionBasis(B,prec);
   if k eq 2 then return F; end if;
   w := ScalingForm(p : Precision := prec);
   return Reverse([ F[i]*w : i in [1..#F] ]);
end intrinsic;

intrinsic ScalingForm(p::RngIntElt : Precision := 100) -> RngSerElt
   {}
   PS<q> := LaurentSeriesRing(RationalField());
   QS<r> := PuiseuxSeriesRing(RationalField());
   prec := Precision;
   if p mod 12 eq 1 then
      t := ((p+1) div 2) mod 4;
      B := EchelonSequence( 
              TwistedBinaryThetaSequence(-4*p,4,t 
                 : Precision := 4*prec) );
      require #B ne 0 :
         "Level does not have sufficient binary quadratic forms"; 
      w := Evaluate(B[#B],r^(1/4));
      return PS ! 
         ( w / DedekindEta(q,[<1,3>,<p,3>] : Precision := prec) );
   elif p mod 12 eq 5 then
      M := BrandtModule(BrandtModuleDatabase(),p,1);
      B := EchelonSequence(ModularFormsBasis(M,2,-1 : Precision := prec));
      w := B[#B];
      return PS !
         ( w / DedekindEta(q,[<1,4>,<p,4>] : Precision := prec) );
   elif p mod 24 eq 7 then
      B := EchelonSequence(BinaryThetaSequence(-p));
      require #B ne 0 :
         "Level does not have sufficient binary quadratic forms"; 
      w := B[#B];
      return PS !
         ( w / DedekindEta(q,[<1,3>,<p,3>] : Precision := prec) );
   elif p mod 24 eq 19 then
      B := EchelonSequence(
              TwistedBinaryThetaSequence(-p,2,1 
                 : Precision := 2*prec) );
      w := Evaluate(B[#B],r^(1/2));
      return PS !
         ( w / DedekindEta(q,[<1,3>,<p,3>] : Precision := prec) ); 
   elif p mod 12 eq 11 then
      return PS ! 
         ( 1 / DedekindEta(q,[<1,2>,<p,2>] : Precision := prec) ); 
   end if;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                // 
//                          RELATIONS                             // 
//                                                                // 
////////////////////////////////////////////////////////////////////

intrinsic FunctionRelations(X::CrvMod : 
   Ngens := 3, UseEisenstein := false, Groebner := true, 
   Precision := 100) -> SeqEnum {}
   // Assumes the input sequence has poles only at cusp at infinity.
   p := Level(X); 
   if not assigned X`BrandtModule then
      require IsPrime(p) : "Argument 1 must have prime level.";
      Dat := BrandtModuleDatabase();
      X`BrandtModule := BrandtModule(Dat,p,1);
   end if;
   prec := Precision; 
   B0 := ModularFormsBasis(X`BrandtModule,0,1 : 
      UseEisenstein := UseEisenstein, Precision := prec );
   // if p = 11 mod 12 then 1 is the first element -- 
   // the Dedekind eta holomorphic form shows up among 
   // anti-invariant forms.
   if p mod 12 eq 11 then Remove(~B0,1); end if;
   B1 := ModularFormsBasis(X`BrandtModule,0,-1 : Precision := prec);
   print "ord0 =", [ -Valuation(f) : f in B0 ];
   print "ord1 =", [ -Valuation(f) : f in B1 ];
   require #B0 ge Ngens : 
      "Number of generators must be at least parameter Ngens.";
   ngens := Ngens;
   A := FreeAbelianMonoid(1);
   M := AbelianMonoid([ A![-Valuation(B0[i])] : i in [1..ngens]]);
   X`CuspidalMonoid := M;
   ords := [ -Valuation(x) : x in B0 ];
   require GCD(ords[1..ngens]) eq 1 : 
      "Parameter Ngens too small: GCD of valuations not 1.";
   // Extend the sequence up to a reasonable size:
   if ngens gt 1 then
      require #ords gt 1 : "Insufficient generators.";
      nmax := ords[ngens-1]*ords[ngens];
   else 
      nmax := ords[ngens];
      require ords[1] eq 1 : 
         "Ngens can not equal 1 if X_0^+(p) is not of genus 0";
   end if;
   // Extend the sequence further...
   nmax := 100;
   // This situation needs to be corrected by having a dynamic 
   // expansion routine.  The modular curve itself should give
   // arbitrarily long plus and minus expansions at infinity --
   // and at various cusps simultaneously. 
   if #B1 gt 0 then
      nmax := Max(nmax,-2*Valuation(B1[1])); 
   end if;
   Bmax := Max(ords);
   ords cat:= [Bmax+1..nmax]; 
   q := Universe(B0).1;
   fncs := B0[1..ngens]; 
   C := CoveringMonoid(M); u := C!0; 
   mon_reps := [ C.i : i in [1..ngens] ];
   mon_reps_seq := [ Representations(M,A![n]) : n in ords ]; 
   true_gaps := [ n : n in [1..Max(ords)] | n notin ords ];
   dfcy_gaps := [ n : n in [1..Max(ords)] | 
                      n notin ords or #mon_reps_seq[Index(ords,n)] eq 0 ];
   require (Max([0] cat dfcy_gaps) + Min(ords)) le Max(ords) : 
      "Parameter Ngens does not specify a sufficient number of generators.";
   for i in [ngens+1..#ords] do
      n := ords[i];
      if #mon_reps_seq[i] gt 0 then
         rep := mon_reps_seq[i][1];
         Append(~mon_reps,rep);
         Append(~fncs,&*[ B0[i]^e[i] : i in [1..ngens] ] 
            where e := Eltseq(rep));
      else 
         if not IsDefined(B0,i) then 
            print "Caution: missing gap n =", n;
   	    print "Ngens =", ngens;
   	    print "ords[1..ngens] =", ords[1..ngens];
            require false : "Invalid gap";
         else 
            Append(~mon_reps,u);
            Append(~fncs,B0[i]);
         end if;
      end if;
   end for;
   I := [ i : i in [1..#mon_reps] | mon_reps[i] eq u ];
   F := FunctionField(Integers(),ngens+1);
   AssignNames(~F,[ "x" * IntegerToString(j) : j in [1..ngens+1] ]);
   f1 := fncs[1];
   x1 := F.1;
   if #I eq 0 then 
      elts := [ &*[ F.j^e[j] : j in [1..ngens] ] 
	      where e is Eltseq(mon_reps[i]) : i in [1..#mon_reps] ];
   else 
      P := PolynomialRing(F,#I);
      AssignNames(~P,[ "T" * IntegerToString(j) : j in [1..#I] ]);
      elts := [ P | ];
      for i in [1..#fncs] do
         if i notin I then
            e := Eltseq(mon_reps[i]);
            elts[i] := &*[ P!F.k^e[k] : k in [1..ngens] ]; 
            fncs[i] := &*[ fncs[k]^e[k] : k in [1..ngens] ]; 
         else 
            elts[i] := P.Index(I,i);
         end if;
      end for;
      mons := [ P | P.j : j in [1..#I] ];
      for i in I do
         j := Index(I,i);   
         n0 := ords[1] + ords[i];
         V := LinearRelations( [ x + O(q^2) : x in 
                [ f1*fncs[i], 1 ] cat fncs | n0 ge Abs(Valuation(x)) ] );
if Dimension(V) eq 0 then
   print [ Valuation(x) : x in 
       [ f1*fncs[i], 1 ] cat fncs | n0 ge Abs(Valuation(x)) ];
   print [ x + O(q^2) : x in 
       [ f1*fncs[i], 1 ] cat fncs | n0 ge Abs(Valuation(x)) ];
   require false : "Dimension 0 error";
end if;
         v := Basis(V)[1];
         c0 := v[2];
         c := e[3..#e] where e is Eltseq(v);
         rel :=  x1*elts[i] + c0 + &+[ c[k]*elts[k] : k in [1..#c] ];
         den := MonomialCoefficient(rel,P.j);
         mons[j] := (den*P.j-rel)/den;
         for k in [1..#mons] do
            mons[k] +:= MonomialCoefficient(mons[k],P.j)*(mons[j]-P.j); 
         end for;
         for k in [1..#elts] do
            elts[k] +:= MonomialCoefficient(elts[k],P.j)*(mons[j]-P.j); 
         end for;
      end for;
      ChangeUniverse(~elts,F);
   end if;
   plus_fld_rels := [ F | ];
   for mon_rel in M`GroebnerRelations do
      m1, m2 := Explode([ C!m : m in mon_pair ]) 
         where mon_pair := Monomials(mon_rel);
      e1 := Eltseq(m1);
      t1 := &*[ fncs[i]^e1[i] : i in [1..ngens] ];
      f1 := &*[ elts[i]^e1[i] : i in [1..ngens] ];
      e2 := Eltseq(m2);
      t2 := &*[ fncs[i]^e2[i] : i in [1..ngens] ]; 
      f2 := &*[ elts[i]^e2[i] : i in [1..ngens] ];
      require Min([ RelativePrecision(f)+Valuation(f) : f in fncs ]) gt 0 
          : "Precision loss.";
      V := LinearRelations( [ 
              x + O(q^2) : x in [ t1-t2, 1 ] cat fncs ] );
      for v in Basis(V) do
         rel := c[1]*(f1-f2) + c[2] + 
            &+[ c[k+2]*elts[k] : k in [1..#elts] ] 
               where c := Eltseq(v);
         Append(~plus_fld_rels,rel);
      end for;
   end for;
   minus_fld_rels := [ F | ];
   if #B1 gt 0 then
      V := LinearRelations( [ 
              x + O(q^2) : x in [ B1[1]^2, 1 ] cat fncs ] );
      for v in Basis(V) do
            rel := c[1]*F.(ngens+1)^2 + c[2] + 
            &+[ c[k+2]*elts[k] : k in [1..#elts] ] 
               where c := Eltseq(v);
         Append(~minus_fld_rels,rel);
      end for;
   end if;
   // PZ := Parent(Numerator(F.1));
   PZ := ChangeRing(Parent(Numerator(F.1)),RationalField());
   plus_fld_rels := [ PZ | Numerator(f) : f in plus_fld_rels ];
   if Groebner then
      minus_fld_rels := [ PZ | NormalForm(PZ!Numerator(f),I) : 
         f in minus_fld_rels ] where I := ideal< PZ |  plus_fld_rels >;
   else
      minus_fld_rels := [ PZ | Numerator(f) : f in minus_fld_rels ];
   end if;
   w := ScalingForm(p : Precision := prec);
   e2 := ( Eisenstein(2,q + O(q^(prec+1))) 
           - p*Eisenstein(2,q^p + O(q^(prec+1))) ) * w;
//   print "e2 =", e2 + O(q);
   e4 := ( Eisenstein(4,q + O(q^(prec+1))) 
             + p^2*Eisenstein(4,q^p + O(q^(prec+1))) ) * w^2;
   f4 := ( Eisenstein(4,q + O(q^(prec+1))) 
             - p^2*Eisenstein(4,q^p + O(q^(prec+1))) ) * w^2;
//   print "e4 =", e4 + O(q);
   e6 := ( Eisenstein(6,q + O(q^(prec+1))) 
             - p^3*Eisenstein(6,q^p + O(q^(prec+1))) ) * w^3;
//   print "e6 =", e6 + O(q);
   f6 := ( Eisenstein(6,q + O(q^(prec+1))) 
             + p^3*Eisenstein(6,q^p + O(q^(prec+1))) ) * w^3;
   print "f6 =", f6*B1[1] + O(q);
   eis_plus := [ Universe(B0) | e2, e4, e6 ];
   eis_minus := [ Universe(B0) | f4, f6 ];
   eis_rels := [ F | ];
   for k in [1..3] do
      V := LinearRelations( [ 
              x + O(q^2) : x in [ -eis_plus[k], 1 ] cat fncs ] );
      v := Basis(V)[1];
      printf "E^+_%o = %o\n", 2*k, v;
      rel := (c[2] + &+[ c[k+2]*elts[k] : k in [1..#elts] ])/c[1] 
                  where c := Eltseq(v);
      Append(~eis_rels,rel);
   end for;   
// This needs to revert to [1..2]!!!
   for k in [1..2] do
      V := LinearRelations( [ x + O(q^2) 
              : x in [ -eis_minus[k]*B1[1], 1 ] cat fncs ] );
      v := Basis(V)[1];
      printf "E^-_%o = %o\n", 2*(k+1), v;
      rel := (c[2] + &+[ c[k+2]*elts[k] : k in [1..#elts] ])
                / ( c[1] * F.(ngens+1) ) where c := Eltseq(v);
      eis_rels[k+1] +:= rel;
   end for;   
   eis_rels := [ PZ | Numerator(f) : f in eis_rels ];
   return plus_fld_rels, minus_fld_rels, eis_rels, elts;
end intrinsic;

/*
intrinsic EisensteinRelation(p::RngIntElt : Precision := 100) -> SeqEnum {}
   require IsPrime(p) : "Argument 1 must be prime";
   require p mod 12 eq 11 : "Argument 1 must be congruent to 11 mod 12.";
   prec := Max(100,Precision);
   PS<q> := LaurentSeriesRing(RationalField());
   E2 := Eisenstein(2,q + O(q^(prec + 1)));
   w := PS!( DedekindEta(q + O(q^(prec+2))) * 
                DedekindEta(q^p + O(q^(prec+p+1))) )^2;
   Dat := BrandtModuleDatabase();
   B := ModularFormsBasis(BrandtModule(Dat,p,1),0,-1
      : Precision := prec);
   return LinearRelations([E2/w] cat B); 
end intrinsic;
*/
