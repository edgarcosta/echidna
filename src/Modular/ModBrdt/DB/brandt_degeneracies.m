//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                   BRANDT MODULE DEGENERACIES DATABASE                    //
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

/* Created by David Kohel, March 2005 */

DATDIR := GetEchidnaDatabaseRoot() * "/ModBrdt/";
prefix := "proj";
level_length := 6;
discr_length := 6;
fullc_length := 3;

//////////////////////////////////////////////////////////////////////////////

import "quaternion_algebras.m" : IsValidLevel;

//////////////////////////////////////////////////////////////////////////////

forward BrandtDegeneraciesDataFile, BrandtDegeneraciesWrite;
forward IsInBrandtDegeneraciesDomain, ExistsBrandtDegeneraciesDataFile;

//////////////////////////////////////////////////////////////////////////////
// Creation function
//////////////////////////////////////////////////////////////////////////////

intrinsic BrandtDegeneraciesDatabase() -> DBUser
    {The Brandt degeneracies database.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Brandt degeneracies";
    Dat`WriteFunction := BrandtDegeneraciesWrite;
    Dat`ExistsFunction := ExistsBrandtDegeneraciesDataFile;
    Dat`IsInDomainFunction := IsInBrandtDegeneraciesDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                             READ ACCESS                                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic DegeneracyMaps(Dat::DBUser, L::[RngIntElt], p::RngIntElt)
    -> SeqEnum, SeqEnum, SeqEnum
    {The sequence of degeneracy matrices for the Brandt module read
    from the Brandt module database.}
    require Dat`DBIdentifier eq "Brandt degeneracies" :
        "Argument 1 must be the database of Brandt degeneracies.";
    require #L in {2,3} :
        "Argument 2 must be a sequence of 2 or 3 integers.";
    D, m := Explode(L);
    c := #L eq 3 select L[3] else 1;
    require m mod p eq 0 :
        "Argument 3 must divide the level of the Brandt modules.";
    t, filename := ExistsBrandtDegeneraciesDataFile(<[D,m,c],p>);
    require t : "No Brandt degeneracies data for this module and prime.";
    assert c eq 1;
    if GCD(D,m) eq 1 then
	h1 := BrandtModuleDimension(D,m);
	h0 := BrandtModuleDimension(D,m div p);
    else
	DBQA := QuaternionAlgebraDatabase();
	h1 := ClassNumber(QuaternionIdealClasses(DBQA,D,m));
	h0 := ClassNumber(QuaternionIdealClasses(DBQA,D,m div p));
    end if;
    e := D mod p eq 0 select 1 else 2;
    degen_maps := [ RMatrixSpace(Integers(),h1,h0) | ];
    degen_indxs := [ [ Parent([Integers()|]) | ] : i in [1..e] ];
    degen_isoms := [ MatrixAlgebra(Integers(),4) | ];
    file := POpen("bunzip2 -c " * filename, "r");   
    for k in [1..e] do
	Append(~degen_isoms,Matrix(4,StringToIntegerSequence(Gets(file)))); 
	Pi := RMatrixSpace(Integers(),h1,h0)!0;
	for j in [1..h0] do
	    I := StringToIntegerSequence(Gets(file)); 
	    Append(~degen_indxs[k],I);
	    for i in I do Pi[i,j] := 1; end for;
	end for; 
	Append(~degen_maps,Pi);
    end for;
    return degen_maps, degen_indxs, degen_isoms;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure BrandtDegeneraciesWrite(Lvl,p,degen_indxs,degen_isoms)
    N, m, c := Explode(Lvl);
    D := N div (m*c^3);
    e := D mod p eq 0 select 1 else 2;
    h0 := #degen_indxs[1];
    filename := BrandtDegeneraciesDataFile(D,m,c,p);
    file := Open(filename,"w");
    Flush(file);
    for k in [1..e] do
	M := Eltseq(degen_isoms[k]);
	// print "Writing M =", M;
	Puts(file,&*[ IntegerToString(x) * " " : x in M ]);
	indxs := degen_indxs[k];
	for i in [1..h0] do
	    // print "Writing I =", indxs[i];
	    Puts(file,&*[ IntegerToString(x) * " " : x in indxs[i] ]);    
	end for; 
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

function BrandtDegeneraciesFilename(D,m,c,p)
    N := D*m*c^3;
    subdr := DirectoryPath(N);
    level := IntegerToString(N);   
    discr := IntegerToString(D);   
    fullc := IntegerToString(c);   
    prime := IntegerToString(p);   
    while #level lt level_length do level := "0" cat level; end while;
    while #discr lt discr_length do discr := "0" cat discr; end while;
    while #fullc lt fullc_length do fullc := "0" cat fullc; end while;
    while #prime lt level_length do prime := "0" cat prime; end while;
    suppath := &*[ DATDIR, subdr ];
    dirpath := &*[ DATDIR, subdr, "/", level, "/" ];  
    filename := &*[ level, ".", discr, ".", fullc, ".", prefix, ".", prime, ".db" ];   
    return dirpath * filename, dirpath, suppath;
end function;

function IsInBrandtDegeneraciesDomain(X)
    if Type(X) ne Tup or #X ne 2 then 
	return false, "Argument must be a tuple of length 2.";
    end if;
    L := X[1]; 
    if Type(L) ne SeqEnum or Type(Universe(L)) ne RngInt or #L notin {2,3} then 
	return false, 
	    "Argument first component must be an integer sequence of length 2 or 3.";
    end if;
    D, m := Explode(L);
    c := #L eq 2 select 1 else L[3];
    if not IsValidLevel(D,m,c) then  
	return false, "Argument first component must specify a valid discriminant and conductor.";
    end if;
    p := X[2];
    if Type(p) ne RngIntElt then
	return false, "Argument must have second component an integer.";
    end if;
    return true, "";
end function;

function ExistsBrandtDegeneraciesDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    L := X[1]; p := X[2];
    D, m := Explode(L);
    c := #L eq 2 select 1 else L[3];
    filename, dirpath := BrandtDegeneraciesFilename(D,m,c,p);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function BrandtDegeneraciesDataFile(D,m,c,p)
    filename, dirpath, suppath := BrandtDegeneraciesFilename(D,m,c,p);
    if System("test -d " * suppath) ne 0 then
        System(&*[ "mkdir ", suppath]);
    end if;
    if System("test -d " * dirpath) ne 0 then
        System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;
