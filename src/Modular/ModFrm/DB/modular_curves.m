//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                        MODULAR CURVES DATABASE                           //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/* Created by David Kohel, September 2000 */

DATDIR := GetEchidnaDatabaseRoot() * "/CrvMod/CrvGen";
prefix := "x0";
level_length := 3;

//////////////////////////////////////////////////////////////////////////////

forward ModularPolynomialDataFile, ModularCurveWrite;
forward IsInModularCurveDomain, ExistsModularCurveDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic ModularCurveDatabase() -> DBUser
    {The database of modular curves.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Modular curve";
    Dat`WriteFunction := ModularCurveWrite;
    Dat`ExistsFunction := ExistsModularCurveDataFile;
    Dat`IsInDomainFunction := IsInModularCurveDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                          MODULAR CURVE ACCESS                            //
//////////////////////////////////////////////////////////////////////////////

intrinsic ModularCurve(Dat::DBUser,N::[RngIntElt]) -> RngMPolElt
    {The modular curve of level N = [N1,N2,N3].}

    require Dat`DBIdentifier eq "Modular curve" : 
        "Argument 1 must be a database of modular curve.";
    bool, filename := ExistsModularCurveDataFile(N);
    require bool : "Argument 1 contains no datafile for this level.";
    return ModularCurve(Dat,N,RationalField());
end intrinsic;

function TorsPolyDegree(N)
    deg := EulerPhi(N);
    return N mod 4 eq 2 select deg else deg div 2;
end function;

intrinsic ModularCurve(Dat::DBUser,N::[RngIntElt],K::Fld) -> RngMPolElt
    {The modular curve of level N = [N1,N2,N3].}

    require Dat`DBIdentifier eq "Modular curve" : 
        "Argument 1 must be a database of modular curve.";
    require #N eq 3 and N[[2,3]] eq [1,1] : 
        "Argument 2 must currently be of the form [N,1,1].";
    bool, filename := ExistsModularCurveDataFile(N);
    require bool : "Argument 1 contains no datafile for this level.";
    file := POpen("bunzip2 -c " * filename, "r");   
    // 0. Dimension of ambient projective space
    n := StringToInteger(Gets(file));
    // 1. Defining polynomials for curve.
    PK := PolynomialRing(K,n+1);
    X := PK.1; Y := PK.2; Z := PK.3;
    assert n eq 2;
    // if n eq 3 then W := PK.4; end if;
    // Degrees of polynomials
    degs := StringToIntegerSequence(Gets(file));
    // Read in polynomial
    for deg in degs do
        // Currently assume that #degs eq 1, so we won't form a sequence
        Phi := PK!0;
        // Number of coefficients
        ncoeffs := StringToInteger(Gets(file));
        for v in [1..ncoeffs] do
            // Need to modify this if dimension is > 2.
            i, j, c := Explode(StringToIntegerSequence(Gets(file)));
            Phi +:= c*X^i*Y^j*Z^(deg-i-j);
        end for;
    end for;
    X0 := ModularCurve(ProjectiveSpace(PK),Phi,"Default",N);
    // 2. Cusps.
    // Number of defining equations 
    csp_eqns := [ PK | ];
    degs := StringToIntegerSequence(Gets(file));
    for deg in degs do
        f := PK!0;
	ncoeffs := StringToInteger(Gets(file));
	for v in [1..ncoeffs] do
	    // Need to modify this if dimension is > 2.
	    i, j, c := Explode(StringToIntegerSequence(Gets(file)));
	    f +:= c*X^i*Y^j*Z^(deg-i-j);
	end for;
        Append(~csp_eqns,f);
    end for;
    X0`CuspidalSubscheme := csp_eqns;
    // 3. Atkin-Lehner involutions (and possibly other exceptional
    // automorphisms, which will be denoted with 'level' 1).
    invs := []; 
    lvls := StringToIntegerSequence(Gets(file));
    degs := StringToIntegerSequence(Gets(file));
    for deg in degs do
        inveqns := [ PK | ];
        for k in [1..n+1] do
            f := PK!0;
            ncoeffs := StringToInteger(Gets(file));
	    for v in [1..ncoeffs] do
                // Need to modify this if dimension is > 2.
                i, j, c := Explode(StringToIntegerSequence(Gets(file)));
                f +:= c*X^i*Y^j*Z^(deg-i-j);
            end for;
            Append(~inveqns,f);
	end for;
	Append(~invs,inveqns);
    end for;
    X0`AtkinLehnerLevels := lvls;
    X0`InvolutionImages := invs;
    // 4. Quotients to X0(M).
    inds := []; quos := []; 
    degs := StringToIntegerSequence(Gets(file));
    for deg in degs do
	// Indices [M,1,1] of modular curve.
	Append(~inds,StringToIntegerSequence(Gets(file)));
	print "inds =", inds;
	quoeqns := [ PK | ];
	for k in [1..n+1] do
            f := PK!0;
            ncoeffs := StringToInteger(Gets(file));
	    print "ncoeffs =", ncoeffs;
	    for v in [1..ncoeffs] do
                // Need to modify this if dimension is > 2.
                i, j, c := Explode(StringToIntegerSequence(Gets(file)));
                f +:= c*X^i*Y^j*Z^(deg-i-j);
            end for;
	    Append(~quoeqns,f);
	end for;
	Append(~quos,quoeqns);
    end for;
    X0`QuotientLevels := inds;
    X0`QuotientImages := quos;
    // 5. Elliptic surfaces over X0(N).
    // Number of elliptic polynomials.
    nsrfs := StringToInteger(Gets(file));
    print "nsrfs =", nsrfs;
    ellsrfs := []; elltors := []; ellsngs := [];
    for r in [1..nsrfs] do
        // 4.A. Coefficients of elliptic surface
        ellcoeffs := [ ];
        for s in [1..5] do
	    print "k =", s;
	    deg := StringToInteger(Gets(file));
	    print "deg =", deg;
	    ncoeffs := StringToInteger(Gets(file));
	    print "ncoeffs =", ncoeffs;
            anum := PK!0; 
            for t in [1..ncoeffs] do
                i, j, c := Explode(StringToIntegerSequence(Gets(file)));
                anum +:= c*X^i*Y^j*Z^(deg-i-j);
            end for;
	    print "anum =", anum;
            ncoeffs := StringToInteger(Gets(file));
            aden := PK!0;
            for t in [1..ncoeffs] do
                i, j, c := Explode(StringToIntegerSequence(Gets(file)));
                aden +:= c*X^i*Y^j*Z^(deg-i-j);
            end for;
	    print "aden =", aden;
	    Append(~ellcoeffs,[anum,aden]);
        end for;
        Append(~ellsrfs,ellcoeffs);
        // 4.B. Kernel polynomial of isogeny (X_0(N) only)
        torspoly := [];
        for s in [1..TorsPolyDegree(N[1])+1] do
            deg := StringToInteger(Gets(file));
            anum := PK!0; 
            ncoeffs := StringToInteger(Gets(file));
            for t in [1..ncoeffs] do
                i, j, c := Explode(StringToIntegerSequence(Gets(file)));
                anum +:= c*X^i*Y^j*Z^(deg-i-j);
            end for;
            aden := PK!0;
            ncoeffs := StringToInteger(Gets(file));
            for t in [1..ncoeffs] do
                i, j, c := Explode(StringToIntegerSequence(Gets(file)));
                aden +:= c*X^i*Y^j*Z^(deg-i-j);
            end for;
            Append(~torspoly,[anum,aden]);
        end for;
        Append(~elltors,torspoly);
        // 4.C. Singular locus for particular patch of elliptic surface
        sngloc := [ PK | 0 ];
        degs := StringToIntegerSequence(Gets(file));
        for deg in degs do
            eqnsng := PK!0; 
            ncoeffs := StringToInteger(Gets(file));
            for t in [1..ncoeffs] do
                i, j, c := Explode(StringToIntegerSequence(Gets(file)));
                eqnsng +:= c*X^i*Y^j*Z^(deg-i-j);
            end for;
            Append(~sngloc,eqnsng);
        end for;
        Append(~ellsngs,sngloc);
    end for;
    X0`EllipticSurfaces := ellsrfs;
    X0`ModularInvariants := elltors;
    X0`SingularSubschemes := ellsngs;
    /*
    // 5. Eisenstein series E2, E4, E6
    for k in [2,4,6] do
	resquo := [ Parent([ PK | 0 ]) | ];
	deg := StringToInteger(Gets(file));
	print "deg =", deg;
	numquoeqn := PK!0; 
	ncoeffs := StringToInteger(Gets(file));
	print "Number of coeffs =", ncoeffs;
	for t in [1..ncoeffs] do
	    i, j, c := Explode(StringToIntegerSequence(Gets(file)));
	    numquoeqn +:= c*X^i*Y^j*Z^(deg-i-j);
	end for;
	denquoeqn := PK!0; 
	mcoeffs := StringToInteger(Gets(file));
	print "Number of coeffs =", mcoeffs;
	for t in [1..mcoeffs] do
	    i, j, c := Explode(StringToIntegerSequence(Gets(file)));
	    denquoeqn +:= c*X^i*Y^j*Z^(deg-i-j);
	end for;
	case k: 
	when 2: X0`Eisenstein2 := [numquoeqn,denquoeqn];
	when 4: X0`Eisenstein4 := [numquoeqn,denquoeqn];
	when 6: X0`Eisenstein6 := [numquoeqn,denquoeqn];
	end case;
    end for;
    */
    return X0;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure ModularCurveWrite(X)
    error if true, "Argument admits no write function.";
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function ModularCurveFilename(N)
    level := IntegerToString(N);   
    while #level lt level_length do level := "0" cat level; end while;
    filename := &*[ DATDIR, prefix, ".", level, ".db" ];
    return filename;
end function;

function ModularCurveDataFile(N)
    filename := ModularCurveFilename(N);
    System("touch " * filename);
    return filename;
end function;

function IsInModularCurveDomain(X)
    if Type(X) ne SeqEnum or Type(Universe(X)) ne RngInt or #X ne 3 then
	return false, "Argument must be an integer sequence of length 3";
    end if;
    N, M, P := Explode(X);
    if M ne 1 or P ne 1 then
	return false, "Arugments components 2 and 3 must be 1.";
    end if;
    return true, "";
end function;

function ExistsModularCurveDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    N, M, P := Explode(X); assert M eq 1 and P eq 1;
    filename := ModularCurveFilename(N);
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;
