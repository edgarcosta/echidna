////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         GRAPHS OF ISOGENIES                        //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function VertexAutomorphismCount(E)
   // Returns HALF the number of automorphisms of E.
   RR := BaseRing(E);
   jE := jInvariant(E);
   if jE eq Zero(RR) then
      if Characteristic(RR) eq 2 then
         return 12;
      elif Characteristic(RR) eq 3 then
         return 6;
      end if;
      return 3;
   elif jE eq RR!12^3 then
      return 2;
   end if;
   return 1;
end function;

intrinsic IsogenyGraph(E::CrvEll,p::RngIntElt) -> SeqEnum
   {The graph of p-isogenies of the elliptic curve E.}
   RR := BaseRing(E);
   if Type(RR) eq FldRat then
      return RationalIsogenyGraph(E,p);
   elif Type(RR) eq FldFin then
      return FiniteIsogenyGraph(E,p);
   end if;
   return "Invalid coefficient ring.";
end intrinsic;

intrinsic IsogenyGraph(S::[CrvEll],p::RngIntElt) -> SeqEnum
   {The graph of p-isogenies of the sequence S of elliptic curves.}  
   RR := BaseRing(S[1]);
   if Type(RR) eq FldRat then
      return RationalIsogenyGraph(S,p);
   elif Type(RR) eq FldFin then
      return FiniteIsogenyGraph(S,p);
   end if;
   return "Invalid coefficient ring.";
end intrinsic;

intrinsic RationalIsogenyGraph(E::CrvEll,p::RngIntElt) -> SeqEnum
   {The graph of p-isogenies of the elliptic curve E over the 
   rational numbers.}
   E0 := MinimalModel(E);
   // X0 := ModularCurveX0(p);
   X0 := ModularCurve(ModularCurveDatabase("Canonical"),p);
   IsogenyList := [ ];
   BoundaryCurves := { E0 };
   InteriorCurves := { Parent(E0) | };
   while BoundaryCurves ne {} do
      E1 := Random(BoundaryCurves);
      Exclude(~BoundaryCurves,E1);
      Include(~InteriorCurves,E1);
      SS := ModuliPoints(X0,E1);
      for P in SS do
         E2 := MinimalModel(Codomain(Isogeny(E1,P)));
         Append(~IsogenyList,[E1,E2]);
         if E2 notin InteriorCurves then
            Include(~BoundaryCurves,E2);
         end if;
      end for;
   end while;
   Curves := SetToSequence( SequenceToSet(  &cat IsogenyList ) );
   n := #Curves;
   M := Zero(MatrixAlgebra(RationalField(),n));
   U := [ VertexAutomorphismCount(X) : X in Curves ];   
   for i in [1..n] do
      E1 := Curves[i];
      for j in [1..n] do
         E2 := Curves[j];
         for T in IsogenyList do
            if T eq [ E1,E2 ] then
               M[i,j] +:= U[i]*1/2;
               M[j,i] +:= U[j]*1/2;
            end if;
         end for;
      end for;
   end for;
   return Curves, M;
end intrinsic;

intrinsic FiniteIsogenyGraph(E::CrvEll,p::RngIntElt) -> SeqEnum
   {The graph of p-isogenies of the elliptic curve E over a 
   finite field.}
   // X0 := ModularCurveX0(p);
   X0 := ModularCurve(ModularCurveDatabase("Canonical"),p);
   Curves := [ E ];
   JValues := { jInvariant(E) };
   IsogenyList := [ Parent([ BaseRing(E) | ]) |  ];
   BoundaryCurves := { E };
   while BoundaryCurves ne {} do
      E1 := Random(BoundaryCurves);
      Exclude(~BoundaryCurves,E1);
      SS := ModuliPoints(X0,E1);
      for P in SS do
         E2 := Codomain(Isogeny(E1,P));
         Append(~IsogenyList,[jInvariant(E1),jInvariant(E2)]);
         if jInvariant(E2) notin JValues then
            Append(~Curves,E2);
            Include(~JValues,jInvariant(E2));
            Include(~BoundaryCurves,E2);
         end if;
      end for;
   end while;
   n := #Curves;
   M := Zero(MatrixAlgebra(RationalField(),n));
   U := [ VertexAutomorphismCount(E) : E in Curves ];   
   for i in [1..n] do
      E1 := Curves[i];
      for j in [1..n] do
         E2 := Curves[j];
         for T in IsogenyList do
            if T eq [ jInvariant(E1), jInvariant(E2) ] then
               M[i,j] +:= U[i]*1/2;
               M[j,i] +:= U[j]*1/2;
            end if;
         end for;
      end for;
   end for;
   return Curves, M;
end intrinsic;

intrinsic RationalIsogenyGraph(S::[CrvEll],p::RngIntElt) -> SeqEnum
   {The graph of p-isogenies of the sequence S of elliptic curves  
   over the rational numbers.}
   // X0 := ModularCurveX0(p);
   X0 := ModularCurve(ModularCurveDatabase("Canonical"),p);
   Curves := S;
   IsogenyList := [ ];
   BoundaryCurves := { Parent(S[1]) | };
   InteriorCurves := { Parent(S[1]) | };
   for E in S do 
      if E notin InteriorCurves then
         Include(~BoundaryCurves,E);
      end if;
      while BoundaryCurves ne {} do
         E1 := Random(BoundaryCurves);
         Exclude(~BoundaryCurves,E1);
         Include(~InteriorCurves,E1);
         SS := ModuliPoints(X0,E1);
         for P in SS do
            E2 := MinimalModel(Codomain(Isogeny(E1,P)));
            Append(~IsogenyList,[E1,E2]);
            if E2 notin InteriorCurves then
               Include(~BoundaryCurves,E2);
            end if;
         end for;
      end while;
   end for;
   AllCurves := SetToSequence( SequenceToSet(  &cat IsogenyList ) );
   Curves := Curves cat [ E : E in AllCurves | E notin Curves ];
   n := #Curves;
   M := Zero(MatrixAlgebra(RationalField(),n));
   U := [ VertexAutomorphismCount(E) : E in Curves ];   
   for i in [1..n] do
      E1 := Curves[i];
      for j in [1..n] do
         E2 := Curves[j];
         for T in IsogenyList do
            if T eq [ E1,E2 ] then
               M[i,j] +:= U[i]*1/2;
               M[j,i] +:= U[j]*1/2;
            end if;
         end for;
      end for;
   end for;
   return Curves, M;
end intrinsic;

intrinsic FiniteIsogenyGraph(S::[CrvEll],p::RngIntElt) -> SeqEnum
   {The graph of p-isogenies of the sequence S of elliptic curves  
   over a finite field.}
   // X0 := ModularCurveX0(p);
   X0 := ModularCurve(ModularCurveDatabase("Canonical"),p);
   Curves := [ Parent(S[1]) | ];
   JValues := { BaseRing(S[1]) | };
   IsogenyList := [ Parent([ BaseRing(S[1]) | ]) |  ];
   for E in S do 
      if jInvariant(E) notin JValues then
         BoundaryCurves := { E };
         Append(~Curves,E);
         Include(~JValues,jInvariant(E));
      end if;
      while BoundaryCurves ne {} do
         E1 := Random(BoundaryCurves);
         Exclude(~BoundaryCurves,E1);
         SS := ModuliPoints(X0,E1);
         for P in SS do
            E2 := Codomain(Isogeny(E1,P));
            Append(~IsogenyList,[jInvariant(E1),jInvariant(E2)]);
            if jInvariant(E2) notin JValues then
               Append(~Curves,E2);
               Include(~JValues,jInvariant(E2));
               Include(~BoundaryCurves,E2);
            end if;
         end for;
      end while;
   end for;
   OldJValues := [ jInvariant(E) : E in S ];
   NewCurves := [ E : E in Curves | jInvariant(E) notin OldJValues ];
   Curves := S cat NewCurves;
   n := #Curves;
   M := Zero(MatrixAlgebra(RationalField(),n));
   U := [ VertexAutomorphismCount(E) : E in Curves ];   
   for i in [1..n] do
      E1 := Curves[i];
      for j in [1..n] do
         E2 := Curves[j];
         for T in IsogenyList do
            if T eq [ jInvariant(E1),jInvariant(E2) ] then
               M[i,j] +:= U[i]*1/2;
               M[j,i] +:= U[j]*1/2;
            end if;
         end for;
      end for;
   end for;
   return Curves, M;
end intrinsic;

