//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                      MODULAR CORRESPONDENCE DATABASE                     //
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

DATDIR := GetEchidnaDatabaseRoot() * "/PolMod/";
prefix := "pol";
level_length := 2;
index_length := 3;

//////////////////////////////////////////////////////////////////////////////

forward ModularCorrespondenceDataFile, ModularCorrespondenceWrite;
forward IsInModularCorrespondenceDomain, ExistsModularCorrespondenceDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic ModularCorrespondenceDatabase() -> DBUser
    {The database of modular correspondences.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Modular correspondence";
    Dat`WriteFunction := ModularCorrespondenceWrite;
    Dat`ExistsFunction := ExistsModularCorrespondenceDataFile;
    Dat`IsInDomainFunction := IsInModularCorrespondenceDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                      HECKE CORRESPONDENCE ACCESS                         //
//////////////////////////////////////////////////////////////////////////////

intrinsic ModularCorrespondence(Dat::DBUser,
    ModelType::MonStgElt, N::RngIntElt, p::RngIntElt) -> RngMPolElt
    {The polynomial defining the p-th modular correspondence
    X_0(pN) -> X_0(N) x X_0(N) modular curve X_0(N) of ModelType.}

    require Dat`DBIdentifier eq "Modular correspondence" : 
	"Argument 1 must be a database of modular correspondences.";
    require ModelType in {"Atkin", "Dedekind eta"} : 
	"Argument 2 must in \"Atkin\" and \"Dedekind eta\".";
    bool, filename :=
	ExistsModularCorrespondenceDataFile(<ModelType,N,p>);
    require bool :
	"Argument 1 contains no datafile for these arguments.";
    file := POpen("bunzip2 -c " * filename, "r");   
    P2 := PolynomialRing(Integers(),2 : Global);
    X := P2.1; Y := P2.2;
    F := P2!0;
    strseq := Gets(file);
    while not IsEof(strseq) do
	i, j, c := Explode(StringToIntegerSequence(strseq));
	if i eq j or (N eq p and ModelType eq "Dedekind eta") then
	    F +:= c*X^i*Y^j;
	else 
	    F +:= c*(X^i*Y^j + X^j*Y^i);
	end if;
	strseq := Gets(file);
    end while;
    return F;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure ModularCorrespondenceWrite(F, ModelType_N_p)
    // {Write F to the modular correspondence database.}
    ModelType := ModelType_N_p[1];
    N := ModelType_N_p[2];
    p := ModelType_N_p[3];
    filename := ModularCorrespondenceDataFile(ModelType, N, p);
    file := Open(filename,"w");   
    // Empty the contents of the file, in case it did exist.
    Flush(file);
    // First line is the gram matrix of order 1.
    for m in Monomials(F) do
	i, j := Explode(Exponents(m));
	if (N eq p and ModelType eq "Dedekind eta") or i ge j then
	    monseq := [i,j] cat [ MonomialCoefficient(F,m) ];
	    Puts(file,&*[ IntegerToString(x) * " " : x in monseq ]);
	end if;
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function ModularCorrespondenceFilename(ModelType, N, p)
    if ModelType eq "Atkin" then
	CrrDir := DATDIR * "AtkCrr";
    elif ModelType eq "Dedekind eta" then
	CrrDir := DATDIR * "EtaCrr";
    end if;
    if System("test -d " * CrrDir) ne 0 then
	System(&*[ "mkdir ", CrrDir]);
    end if;
    level := IntegerToString(N);   
    while #level lt level_length do level := "0" cat level; end while;
    index := IntegerToString(p);
    while #index lt index_length do index := "0" cat index; end while;
    filename := &*[ CrrDir, "/", level, "/", prefix, ".", level, ".", index, ".db" ];
    return filename, CrrDir * "/" * level;
end function;

function IsInModularCorrespondenceDomain(X)
    if Type(X) ne Tup or #X ne 3 then 
	return false, "Argument must be a tuple of length 3.";
    end if;
    ModelType := X[1]; N := X[2]; p := X[3];
    case ModelType:
    when "Atkin":
	if N notin {2,3,5,7,11,13,17,19,23,29,31,41,47,59,71} then 
	    return false, "Argument component 3 must in {2,3,5,7,11,13,17,19,23,29,31,41,47,59,71}.";
	end if;
    when "Dedekind eta":
	if N notin {2,3,4,5,7,9,13,25} then
	    return false, "Argument component 3 must in {2,3,4,5,7,9,13,25}.";
	end if;
    else
	return false, "Argument component 2 must be \"Atkin\" or \"Dedekind eta\".";
    end case;
    return true, "";
end function;

function ExistsModularCorrespondenceDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    ModelType := X[1]; N := X[2]; p := X[3];
    filename, dirpath := ModularCorrespondenceFilename(ModelType, N, p);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function ModularCorrespondenceDataFile(ModelType, N, p)
    filename, dirpath := ModularCorrespondenceFilename(ModelType, N, p);
    if System("test -d " * dirpath) ne 0 then
	System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;


