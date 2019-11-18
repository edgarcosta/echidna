//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                   BRANDT MODULE DECOMPOSITION DATABASE                   //
//         Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>         //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/* Created by David Kohel, December 2000 */

DATDIR := GetEchidnaDatabaseRoot() * "/ModBrdt/";
prefix := "dcmp";
discr_length := 6;
level_length := 6;
fullc_length := 3;

//////////////////////////////////////////////////////////////////////////////

import "quaternion_algebras.m" : IsValidLevel;

//////////////////////////////////////////////////////////////////////////////

forward BrandtDecompositionDataFile, BrandtDecompositionWrite;
forward IsInBrandtDecompositionDomain, ExistsBrandtDecompositionDataFile;

//////////////////////////////////////////////////////////////////////////////
// Creation function
//////////////////////////////////////////////////////////////////////////////

intrinsic BrandtDecompositionDatabase() -> DBUser
    {The Brandt module decomposition database.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Brandt decomposition";
    Dat`WriteFunction := BrandtDecompositionWrite;
    Dat`ExistsFunction := ExistsBrandtDecompositionDataFile;
    Dat`IsInDomainFunction := IsInBrandtDecompositionDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function Submodule(M,S)
    // {}
    X := sub< M`Module | S >;
    if X eq M`Module then return M; end if;
    N := New(ModBrdt);
    N`AmbientModule := AmbientModule(M);
    N`Module := X;
    N`IsFull := N`Module cmpeq AmbientModule(M)`Module;
    N`RamifiedPrimes := M`RamifiedPrimes;
    N`Conductor := M`Conductor;
    N`BaseRing := M`BaseRing;
    N`HeckePrecision := 0;
    N`HeckePrimes := [ Integers() | ];
    N`HeckeOperators := [ Mat | ]
        where Mat := MatrixAlgebra(N`BaseRing,Dimension(N`Module));
    // Set some decomposition data in case it doesn't get set later.
    if assigned M`DecompositionIdeal then
        N`DecompositionIdeal := M`DecompositionIdeal;
    else
        print "Warning: DecompositionIdeal not assigned.";
        M`DecompositionIdeal := {@ @};
        N`DecompositionIdeal := {@ @};
    end if;
    return N;
end function;

//////////////////////////////////////////////////////////////////////////////
//                             READ ACCESS                                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic NewSubspaceDecomposition(Dat::DBUser, M::ModBrdt) -> SeqEnum
    {The decomposition submodules of the Brandt module read from 
    the Brandt module database.}
    require Dat`DBIdentifier eq "Brandt decomposition" : 
        "Argument 1 must be the database of Brandt decomposiion.";
    require IsFull(M) : "Argument 2 must be a full Brandt module.";
    N, m, c := Explode(LevelIndices(M));
    D := (N div m) div c^3;
    t, filename := ExistsBrandtDecompositionDataFile([D,m,c]);
    require t : "No decomposition data for this module.";
    S := CuspidalSubspace(M);
    if m ne 1 then
	DBBQ := BrandtDegeneraciesDatabase();
	prms := PrimeDivisors(m);
	M`ConductorPrimes := prms;
	M`DegeneracyIndices := [];
	for k in [1..#prms] do
	    p := prms[k];
	    if <[D,m],p> in DBBQ then
		degen_maps, degen_indxs := DegeneracyMaps(DBBQ,[D,m],p);
		M`DegeneracyIndices[k] := degen_indxs;
		for Pi in degen_maps do
		    S := Kernel(Pi,S);
		end for;
	    end if;
	end for;
    end if;
    file := POpen("bunzip2 -c " * filename, "r");   
    strseq := Gets(file);
    // First line consists of the dimensions of components.
    dims := StringToIntegerSequence(strseq);
    // Following lines are the coordinates of the bases.
    M`NewFactorBases := [ ];
    for d in dims do
        B := [ ];
        for i in [1..d] do
	    strseq := Gets(file);
            Append(~B,StringToIntegerSequence(strseq)); 
        end for; 
        Append(~M`NewFactorBases,B);
    end for;
    M`DecompositionBound := Infinity();
    decomp := [ ];
    for B in M`NewFactorBases do
        N := Submodule(M,[ M`Module!x : x in B ]); 
        N`IsIndecomposable := true;
	if N subset S then
	    Append(~decomp,N);
	else
	    vprint Brandt, 2 : 
		" Discarding old submodule of dimension:", Dimension(N);
	end if;
    end for;
    return decomp;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure BrandtDecompositionWrite(L,dcmp)
    D, m, c := Explode(L); N := D*m*c^3;
    filename := BrandtDecompositionDataFile(D,m,c);
    file := Open(filename,"w");   
    Flush(file);
    // First line consists of the dimensions of the factors.
    dims := [ Dimension(B) : B in dcmp ];
    Puts(file,&cat[ Strings() | IntegerToString(d) * " " : d in dims ]);    
    // Following lines are the coordinates of the bases.
    dcmp_bases := &cat [ [ Eltseq(x) : x in Basis(B) ] : B in dcmp ];
    for B in dcmp_bases do
        Puts(file,&*[ IntegerToString(x) * " " : x in B ]);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function DirectoryPath(N)
    n1 := 400*((N-1) div 400);
    s1 := IntegerToString(n1+1);
    s2 := IntegerToString(n1+400);
    while #s1 lt level_length do s1 := "0" cat s1; end while;
    while #s2 lt level_length do s2 := "0" cat s2; end while;
    return s1 * "-" * s2;    
end function;

function BrandtDecompositionFilename(D,m,c : Extension := "")
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

function IsInBrandtDecompositionDomain(X)
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

function ExistsBrandtDecompositionDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    D, m := Explode(X);
    c := #X eq 2 select 1 else X[3];
    filename, dirpath := BrandtDecompositionFilename(D,m,c);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function BrandtDecompositionDataFile(D,m,c)
    filename, dirpath, suppath := BrandtDecompositionFilename(D,m,c);
    if System("test -d " * suppath) ne 0 then
	System(&*[ "mkdir ", suppath]);
    end if;
    if System("test -d " * dirpath) ne 0 then
        System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;
