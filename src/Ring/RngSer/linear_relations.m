//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//               Linear Relations among Power Series                        //
//         Copyright (C) 2009 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function PrecisionBound(f,max)
    if RelativePrecision(f) eq -1 then
	return max;
    else
	return AbsolutePrecision(f);
    end if;
end function;

function ValuationOrder(f,g)
   // Partial ordering of series based on valuation.
   n := Valuation(f);
   m := Valuation(g);
   if n gt m then return 1;
   elif n lt m then return -1;
   end if;
   return 0;
end function;

intrinsic LinearRelations(S::[RngSerElt]) -> ModTupRng
    {The linear relation space among the series elements of S.}
    n := #S;
    PS := Universe(S); q := PS.1;
    R := BaseRing(PS);
    vprintf SeriesRelations : "Finding linear relations of %o series over %o\n", n, R;
    N := 1000;
    max := 1000;
    while N ge max do
	N := Min([ PrecisionBound(f,max) : f in S ]);
	max +:= 1000;
    end while;
    begin := Min([ Valuation(S[i]) : i in [1..n] ]);
    dim := N - begin;
    vprintf SeriesRelations : "Setting up matrix of size %o x %o\n", n, dim;
    M := Zero(RMatrixSpace(R,n,dim));
    for i in [1..n] do
	for j in [1..dim] do
	    M[i,j] := Coefficient(S[i],begin+j-1);
	end for;
    end for;
    vprint SeriesRelations : "Computing matrix kernel.";
    V := Kernel(M);
    vprintf SeriesRelations : "Found kernel of dimension %o\n", Dimension(V);
    return V;
end intrinsic;

intrinsic EchelonSequence(B::[RngSerElt]) -> SeqEnum
   {Returns the echelonized sequence of power series spanning
   the same space.}

   require IsField(CoefficientRing(Universe(B))) :
      "Series base ring must be a field";
   if #B eq 0 then return B; end if;
   for i in [1..#B] do
      Sort(~B,ValuationOrder);
      n1 := Valuation(B[i]);
      if n1 lt PrecisionBound(B[i],Infinity()) then 
         B[i] := B[i]/Coefficient(B[i],n1);
         for j in [1..#B] do
            if j lt i then
               B[j] := B[j] - Coefficient(B[j],n1)*B[i]; 
            elif j gt i and (n1 eq Valuation(B[j])) then 
               B[j] := B[j] - Coefficient(B[j],n1)*B[i]; 
               n2 := Valuation(B[j]);
               if n2 lt PrecisionBound(B[i],Infinity()) then 
                  B[j] := B[j]/Coefficient(B[j],n2);
               end if;
            end if;
         end for;
      end if;
   end for;         
   while #B gt 0 and RelativePrecision(B[#B]) eq 0 do
      Remove(~B,#B); 
      if #B eq 0 then break; end if; 
   end while; 
   return B;
end intrinsic;


