//////////////////////////////////////////////////////////////////////////////
//                                                                          //
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

import "genus2_curves.m": IsValidFrobeniusCharpoly;

intrinsic ExtendGenus2ZetaFunctionsDatabaseFromCurvesDatabase(
    Dat::DBUser,chi::RngUPolElt[RngInt])
    {}
    require Dat`DBIdentifier eq "Genus 2 zeta functions" : "Argument 1 must be the database of genus 2 zeta functions.";
    if Coefficient(chi,3) gt 0 then chi := Evaluate(chi,-Parent(chi).1); end if;
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool: "Argument 2 is not a valid Frobenius characteristic polynomial.";
    DBG2 := Genus2CurvesDatabase();
    JJ_S := {@ JJ : JJ in &cat IgusaInvariantsSequences(DBG2,chi) @};
    vprint Genus2Curves : "Number of invariants in g2 database:", #JJ_S;
    JJ_Z := Genus2ZetaFunctionsIgusaInvariantsSequence(Dat,chi);
    vprint Genus2Curves : "Number of invariants in z2 database:", #JJ_Z;
    for JJ in JJ_S[[1..#JJ_S by r]] do
	if JJ notin JJ_Z then
	    Write(Dat,chi,JJ : Overwrite);
	end if;
    end for;
end intrinsic;

intrinsic ExtendGenus2ZetaFunctionsDatabase(Dat::DBUser,chi::RngUPolElt[RngInt] :
    IsogenyPrime := 0, ExtensionDegree := 1, IsogenyDepth := 1)
    {Extend the database of known invariants with given Frobenius charpoly chi by
    (p,p)-isogenies, where p runs through [2,3] or equals the given IsogenyPrime.}

    require Dat`DBIdentifier eq "Genus 2 zeta functions" : "Argument 1 must be the database of genus 2 zeta functions.";
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool : "Argument 2 must be a Frobenius characteristic polynomial.";
    require Type(ExtensionDegree) eq RngIntElt and ExtensionDegree ge 1 :
	"Parameter \"ExtensionDegree\" must be a positive integer.";
    FF := FiniteField(p,r);
    KK := ExtensionDegree gt 1 select FiniteField(p,ExtensionDegree*r) else FF;
    q_seq := IsogenyPrime ne 0 select [ IsogenyPrime ] else p eq 3 select [2] else [2,3];
    JJ_seq := Genus2ZetaFunctionsIgusaInvariantsSequence(Dat,chi);
    X := { Parent([ KK | ]) | };
    s := ExtensionDegree;
    if s eq 1 then
	Z := { IgusaToAbsoluteIgusaInvariants(JJ) : JJ in JJ_seq };
    else
	Z := { IgusaToAbsoluteIgusaInvariants(ChangeUniverse(JJ,KK)) : JJ in JJ_seq };
    end if;
    if GetVerbose("Genus2ZetaFunctions") gt 0 then
	print "Known number of invariants:", #Genus2ZetaFunctionsIgusaInvariantsSequence(Dat,chi);
    end if;
    for q in q_seq do
	Extended := false;
	vprintf Genus2ZetaFunctions : "Extending by (%o,%o)-isogenies.\n", q, q;
	n := #JJ_seq div r;
	Frontier_new := { IgusaToAbsoluteIgusaInvariants(JJ_seq[j]) : j in [(k-1)*r+1 : k in [1..n]] };
	if s gt 1 then
	    Frontier_new := { ChangeUniverse(jj,KK) : jj in Frontier_new };
	end if;
	for depth in [1..IsogenyDepth] do
	    Frontier := Frontier_new;
	    Frontier_new := { };
	    vprintf Genus2ZetaFunctions : "Depth %2o: Extending frontier of size %o\n", depth, #Frontier;
	    for jj in Frontier do
		if jj in X then continue; end if;
		V := AbsoluteIgusaToIsogenousInvariants(jj,q);
		Y := { jj : jj in V | jj notin X and jj notin Z };
		if #Y gt 0 then
		    vprintf Genus2ZetaFunctions : "Found %o new isogenous invariants.\n", #Y;
		    Extended := true;
		end if;
		Frontier_new join:= Y;
		for jj in Y do
		    if jj in X or jj in Z then continue; end if;
		    jj_orbit := { [ j^(p^k) : j in jj ] : k in [0..s*r-1] };
		    X join:= jj_orbit;
		    m := #jj_orbit;
		    if m lt r then
			printf "Igusa invariants defined over smaller field of degree %o.\n", m;
			kk := ChangeUniverse(jj,FiniteField(p,m));
			C := HyperellipticCurveFromAbsoluteIgusaInvariants(kk);
			xi := FrobeniusCharacteristicPolynomial(C);
			if Coefficient(chi,3) gt 0 then
			    C := QuadraticTwist(C);
			    xi := FrobeniusCharacteristicPolynomial(C);
			end if;
			Write(Dat,xi,C : Overwrite);
			continue;
		    elif m eq r then
			kk := ChangeUniverse(jj,FF);
			C := HyperellipticCurveFromAbsoluteIgusaInvariants(jj);
			if FrobeniusCharacteristicPolynomial(C) ne chi then
			    C := QuadraticTwist(C);
			end if;
			Write(Dat,chi,C : Overwrite);
		    end if;
		end for;
	    end for;
	end for;
	if GetVerbose("Genus2ZetaFunctions") gt 0 and Extended then
	    print "Currently known invariant numbers:", #Genus2ZetaFunctionsIgusaInvariantsSequence(Dat,chi);
	end if;
    end for;
end intrinsic;
