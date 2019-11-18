//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                        BRANDT MODULE DATABASE                            //
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

/* Created by David Kohel, May 2000 */

DATDIR := GetEchidnaDatabaseRoot() * "/ModBrdt/";
prefix := "brdt";
discr_length := 6;
level_length := 6;
fullc_length := 3;

//////////////////////////////////////////////////////////////////////////////

import "quaternion_algebras.m" : IsValidLevel;

//////////////////////////////////////////////////////////////////////////////

forward BrandtModuleDataFile, BrandtModuleWrite;
forward IsInBrandtModuleDomain, ExistsBrandtModuleDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic BrandtModuleDatabase() -> DBUser
    {The Brandt module database.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Brandt module";
    Dat`WriteFunction := BrandtModuleWrite;
    Dat`ExistsFunction := ExistsBrandtModuleDataFile;
    Dat`IsInDomainFunction := IsInBrandtModuleDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function BrandtModule_init(prms, m, r, auts, grams)
    h := #auts;
    M := New(ModBrdt);
    M`IsFull := true;
    M`RamifiedPrimes := prms;
    M`Conductor := m;
    M`FullLevelIndex := r;
    M`BaseRing := Integers();
    M`NormGrams := grams;
    M`AutoNums := auts;
    M`HeckePrecision := 0;
    M`ThetaSeries := [ LaurentSeriesRing(Integers()) | ];
    M`HeckePrimes := [ Integers() | ];
    MatZ := MatrixAlgebra(Integers(),h);
    M`HeckeOperators := [ MatZ | ];
    M`Module := RSpace(Integers(),h,
	DiagonalMatrix(MatZ, [ n div 2 : n in auts]));
    M`DecompositionIdeal := {@ @};
    return M;
end function;

//////////////////////////////////////////////////////////////////////////////
//                             READ ACCESS                                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic BrandtModule(Dat::DBUser,D::RngIntElt,m::RngIntElt) -> ModBrdt
    {The Brandt module of a quaternion order of conductor m in 
    the quaternion algebra of discriminant D.}

    require Dat`DBIdentifier eq "Brandt module" : 
	"Argument 1 must be the database of Brandt modules.";
    val, error_message := IsValidLevel(D,m,1);
    require val : error_message;
    old_data := true;
    t, filename := ExistsBrandtModuleDataFile([D,m,1]);
    require t : "No data file for this discriminant and level";
    file := POpen("bunzip2 -c " * filename, "r");   
    strseq := Gets(file);
    // First line should be the line of automorphism numbers.
    auts := StringToIntegerSequence(strseq);
    // Remaining lines give the matrices.
    MatZ := MatrixAlgebra(Integers(),4);
    grams := [ MatZ | ];
    strseq := Gets(file);
    if #StringToIntegerSequence(strseq) eq 16 then
	old_data := true;
    else 
	old_data := false;
	r := #auts div 2; 
	auts := &cat[
	    [ auts[2*j] : i in [1..auts[2*j-1] ] ] : j in [1..r] ];
    end if;
    while not IsEof(strseq) do
	Q := StringToIntegerSequence(strseq);
	if old_data then 
	    Append(~grams,MatZ!Q);
	else 
	    Append(~grams,SymmetricMatrix(Q));
	end if;
	strseq := Gets(file);
    end while;
    prms := PrimeDivisors(D);
    M := BrandtModule_init(prms, m, 1, auts, grams);
    DBQA := QuaternionAlgebraDatabase();
    if [D,m] in DBQA then
	Q := QuaternionIdealClasses(DBQA,D,m);
	M`LeftIdeals := LeftIdealClasses(Q);
    end if;
    prms := PrimeDivisors(m);
    M`ConductorPrimes := prms;
    M`DegeneracyIndices := [];
    DBBQ := BrandtDegeneraciesDatabase();
    for i in [1..#prms] do
	p := prms[i];
	if <[D,m],p> in DBBQ then
	    _, degen_indxs := DegeneracyMaps(DBBQ,[D,m],p);
	    M`DegeneracyIndices[i] := degen_indxs;
	end if;
    end for;
    return M;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure BrandtModuleWrite(M)
    error if not IsFull(M), "Argument must not be a proper submodule.";
    N, m, c := Explode(LevelIndices(M));
    D := (N div m) div c^3;
    filename := BrandtModuleDataFile(D,m,c);
    file := Open(filename,"w");   
    // Empty the contents of the file, in case it did exist.
    Flush(file);
    // First line should be the numbers of automorphisms.
    m := 1;
    auts := M`AutoNums;
    auts_count := [ Integers() | ];
    for k in [1..#auts] do
	if k+1 le #auts and auts[k] eq auts[k+1] then
	    m +:= 1;
	else
	    auts_count cat:= [ m, auts[k] ];
	    m := 1;
	end if; 
    end for;
    Puts(file,&*[ IntegerToString(x) * " " : x in auts_count ]);    
    // Following lines are the gram matrices of the norm lattices.
    for A in M`NormGrams do
	S := &cat[ [ A[i,j] : j in [1..i] ] : i in [1..4] ];
	matstr := &*[ IntegerToString(x) * " " : x in S ];
	Puts(file,matstr);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                              FILE STRUCTURE                              //
//////////////////////////////////////////////////////////////////////////////

function DirectoryPath(N)
    n1 := 400*((N-1) div 400);
    s1 := IntegerToString(n1+1);
    s2 := IntegerToString(n1+400);
    while #s1 lt level_length do s1 := "0" cat s1; end while;
    while #s2 lt level_length do s2 := "0" cat s2; end while;
    return s1 * "-" * s2;    
end function;

function BrandtModuleFilename(D,m,c : Extension := "")
    N := D*m*c^3;
    subdr := DirectoryPath(N);
    level := IntegerToString(N);   
    discr := IntegerToString(D);   
    fullc := IntegerToString(c);   
    while #level lt level_length do level := "0" cat level; end while;
    while #discr lt discr_length do discr := "0" cat discr; end while;
    while #fullc lt fullc_length do fullc := "0" cat fullc; end while;
    suppath := &*[ DATDIR, subdr ];
    dirpath := &*[ DATDIR, subdr, "/", level, "/" ];  
    filename := &*[ level, ".", discr, ".", fullc, ".", prefix, ".db" ];   
    return dirpath * filename, dirpath, suppath;
end function;

function IsInBrandtModuleDomain(X)
    if Type(X) ne SeqEnum or Type(Universe(X)) ne RngInt or #X notin {2,3} then 
	return false, "Argument must be an integer sequence of length 2 or 3.";
    end if;
    D, m := Explode(X);
    c := #X eq 2 select 1 else X[3];
    if not IsValidLevel(D,m,c) then  
	return false, "Argument must specify a valid discriminant and conductor.";
    end if;
    return true, "";
end function;

function ExistsBrandtModuleDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    D, m := Explode(X);
    c := #X eq 2 select 1 else X[3];
    filename, dirpath := BrandtModuleFilename(D,m,c);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function BrandtModuleDataFile(D,m,c)
    filename, dirpath, suppath := BrandtModuleFilename(D,m,c);
    if System("test -d " * suppath) ne 0 then
	System(&*[ "mkdir ", suppath]);
    end if;
    if System("test -d " * dirpath) ne 0 then
	System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;

