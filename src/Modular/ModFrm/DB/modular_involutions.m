//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                      DEDEKIND ETA INVOLUTION DATABASE                    //
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

/* Created by David Kohel, June 2001 */

DATDIR := GetEchidnaDatabaseRoot() * "/PolMod/";
prefix := "inv";
level_length := 3;

////////////////////////////////////////////////////////////////////////

forward ModularInvolutionDataFile, ModularInvolutionWrite;
forward IsInModularInvolutionDomain, ExistsModularInvolutionDataFile;

//////////////////////////////////////////////////////////////////////////////
//                       CREATION FUNCTION                                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic ModularInvolutionDatabase() -> DBUser
    {The database of modular involutions of X_0(N).}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Modular involution";
    Dat`WriteFunction := ModularInvolutionWrite;
    Dat`ExistsFunction := ExistsModularInvolutionDataFile;
    Dat`IsInDomainFunction := IsInModularInvolutionDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                      CANONICAL INVOLUTION ACCESS                         //
//////////////////////////////////////////////////////////////////////////////

intrinsic ModularInvolution(Dat::DBUser,ModelType::MonStgElt,
    N::RngIntElt) -> RngMPolElt
    {The polynomial defining the modular involution on the modular
    curve X_0(N) of type ModelType and prime level N.}

    require Dat`DBIdentifier eq "Modular involution" : 
       "Argument 1 must be a database of modular involutions.";
    bool, filename := ExistsModularInvolutionDataFile(<ModelType,N>);
    require bool :
	"Argument 1 contains no datafile for these arguments.";
    file := POpen("bunzip2 -c " * filename, "r");   
    P2 := PolynomialRing(Integers(),2 : Global);
    X := P2.1; J := P2.2;
    poly := [ P2 | ];
    // First line gives the degrees in X of the coefficients of J^i,
    // with the last polynomial in X as the denominator.
    strseq := Gets(file);
    degs := StringToIntegerSequence(strseq);
    for n in degs do
	F := P2!0;
	for i in [0..n] do
	    strseq := Gets(file);
	    F +:= StringToInteger(strseq)*X^i;
	end for;;
	Append(~poly, F);
    end for;
    return [ &+[ poly[i]*J^(i-1) : i in [1..#degs-1] ], poly[#degs] ];
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                         ACCESSORY FUNCTIONS                              //
//////////////////////////////////////////////////////////////////////////////

procedure ModularInvolutionPairWrite(jnum_jden,ModelType_N)
    // {Write F to the modular involution database.}
    ModelType := ModelType_N[1]; N := ModelType_N[2];
    filename := ModularInvolutionDataFile(ModelType,N);
    file := Open(filename,"w");   
    // 
    jnum := jnum_jden[1]; jden := jnum_jden[2];
    // Empty the contents of the file, in case it did exist.
    Flush(file);
    // First line is the gram matrix of order 1.
    ZZ := Integers();
    FQ := FunctionField(RationalField());
    PQ := PolynomialRing(RationalField());
    polys := [ PQ!(FQ!f) : f in Eltseq(jnum) ] cat
             [ PQ!(FQ!Eltseq(jden)[1]) ];
    Puts(file,&*[ IntegerToString(Degree(Fi)) * " " : Fi in polys ]);
    for Fi in polys do
	for j in [0..Degree(Fi)] do
	    Puts(file,IntegerToString(ZZ!Coefficient(Fi,j)));
	end for;
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

procedure ModularInvolutionWrite(j1,ModelType_N)
    // {Write F to the modular involution database.}
    if Type(j1) in {Tup,Seq} then
	ModularInvolutionPairWrite(j1,ModelType_N); return;
    end if;
    ModelType := ModelType_N[1]; N := ModelType_N[2];
    filename := ModularInvolutionDataFile(ModelType,N);
    file := Open(filename,"w");   
    // Empty the contents of the file, in case it did exist.
    Flush(file);
    // First line is the gram matrix of order 1.
    ZZ := Integers();
    FQ := FunctionField(RationalField());
    PQ := PolynomialRing(RationalField());
    jseq := [ FQ!x : x in Eltseq(j1) ];
    jden := LCM([ Denominator(f) : f in jseq ]);
    polys := [ PQ!(jden*f) : f in jseq ] cat [ jden ];
    Puts(file,&*[ IntegerToString(Degree(Fi)) * " " : Fi in polys ]);
    for Fi in polys do
	for j in [0..Degree(Fi)] do
	    Puts(file,IntegerToString(ZZ!Coefficient(Fi,j)));
	end for;
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

function ModularInvolutionFilename(ModelType,N)
    level := IntegerToString(N);
    if ModelType eq "Atkin" then
	InvDir := "AtkInv";
    elif ModelType eq "Dedekind eta" then
	InvDir := "EtaInv";
    else
	error "No known modular involutions for ModelType " * ModelType;
    end if;
    while #level lt level_length do level := "0" cat level; end while;
    dirpath := DATDIR * InvDir * "/";
    filename := &*[ dirpath, prefix, ".", level, ".db" ];
    return filename, dirpath;
end function;

function IsInModularInvolutionDomain(X)
    if Type(X) ne Tup or #X ne 2 then
	return false, "Argument must be an tuple of length 2.";
    end if;
    ModelType := X[1];
    N := X[2];
    if Type(ModelType) ne MonStgElt or Type(N) eq RngIntElt then 
	return false,
	    "Argument must be an tuple consisting of a string and an integer.";
    elif ModelType notin {"Atkin","Dedekind eta"} then 
	return false, "Argument component 1 must be \"Atkin\" or \"Dedekind eta\"";
    end if;
    return true, "";
end function;

function ExistsModularInvolutionDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    ModelType := X[1];
    N := X[2];
    filename, dirpath := ModularInvolutionFilename(ModelType,N);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function ModularInvolutionDataFile(ModelType,N)
    filename, dirpath := ModularInvolutionFilename(ModelType,N);
    if System("test -d " * dirpath) ne 0 then
	System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;

