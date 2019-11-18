//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                           LATTICE GENERA DATABASE                        //
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

DATDIR := GetEchidnaDatabaseRoot() * "/SymGen/";
prefix := "gen";
rnk_length := 2;
det_length := 6;

//////////////////////////////////////////////////////////////////////////////

forward LatticeGeneraDataFile, LatticeGeneraWrite;
forward IsInLatticeGeneraDomain, ExistsLatticeGeneraDataFile;
forward ExistsLatticeGeneraDataObject;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic LatticeGeneraDatabase() -> DBUser
    {The database of genera of lattices.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Lattice genera";
    Dat`WriteFunction := LatticeGeneraWrite;
    Dat`ExistsFunction := ExistsLatticeGeneraDataObject;
    Dat`IsInDomainFunction := IsInLatticeGeneraDomain;
    return Dat;
end intrinsic;

/*
Note: Since the genera a stored together in terms of rank and discriminant,
for membership in database, it is necessary to test not only whether a file
exists, but whether the object is stored in the file.  Hence the function
ExistsLatticeGeneraDataObject in addition to ExistsLatticeGeneraDataFile.
*/

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function Genus_init(latseq)
    G := Genus(latseq[1]);
    G`Representatives := latseq;
    return G;
end function;

//////////////////////////////////////////////////////////////////////////////
//                             READ ACCESS                                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic LatticeGenera(
    Dat::DBUser,r::RngIntElt,D::RngIntElt) -> SeqEnum
    {The sequence of genera of lattices of rank r and discriminant D.}
    require Dat`DBIdentifier eq "Lattice genera" : 
	"Argument 1 must be a database of lattice genera.";
    bool, filename := ExistsLatticeGeneraDataFile(r,D);
    genera := [ PowerStructure(SymGen) | ];
    if not bool then
	return genera;
    end if;
    file := POpen(&*["bunzip2 -c ", filename ], "r");
    MatZ := MatrixAlgebra(Integers(),r);
    strseq := Gets(file);
    while not IsEof(strseq) do
	lats := [ ];
	// First line should be the number of genus representatives
	for k in [1..StringToInteger(strseq)] do
	    strseq := Gets(file);
	    A := MatZ!StringToIntegerSequence(strseq);
	    Append(~lats,LatticeWithGram(A));
	end for; 
	Append(~genera,Genus_init(lats)); 
	strseq := Gets(file);
    end while;
    delete file; // Explicitly close file
    return genera;
end intrinsic; 

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure LatticeGeneraWrite(S)
    case Type(S):
    when Lat:
	S := [ Genus(S) ];
    when SymGen:
	S := [ S ];
    when SeqEnum:
	if #S eq 0 then return; end if;
	error if not Type(S[1]) eq SymGen, "Argument must be a sequence of lattice genera.";
    else:
	error if true, "Argument must be a sequence of lattice genera.";
    end case;
    if #S eq 0 then return; end if;
    r := Rank(S[1]);
    D := Determinant(S[1]);
    // Read and append the current data...
    T := LatticeGenera(LatticeGeneraDatabase(),r,D);
    k := 0;
    for G in S do
	if &or[ G eq H : H in T ] then
	    k +:= 1;
	else
	    Append(~T,G);
	end if;
    end for;   
    // Check if all genera are in the database (hence done):
    if k eq #S then return; end if;
    // Get file for writing...
    filename := LatticeGeneraDataFile(r,D);
    file := Open(filename,"w");
    for G in T do
	n := #Representatives(G);
	Puts(file,IntegerToString(n));
	for L in Representatives(G) do 
	    A := GramMatrix(L);
	    matstr := &*[ IntegerToString(x) * " " : x in Eltseq(A) ];
	    Puts(file,matstr);
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

function GeneraFilename(r,D)
    rnk := IntegerToString(r);   
    det := IntegerToString(D);   
    while #det lt det_length do det := "0" cat det; end while;
    while #rnk lt rnk_length do rnk := "0" cat rnk; end while;
    dirpath := DATDIR * rnk * "/";
    filename := &*[ dirpath, prefix, ".", rnk, ".", det, ".db" ];
    return filename, dirpath; 
end function;

function IsInLatticeGeneraDomain(G)
    if Type(G) eq SymGen then
	return true, "";
    end if;
    return false, "Argument must be the genus of a lattice.";
end function;

function ExistsLatticeGeneraDataObject(G)
    // Returns true if and only if the compressed data file exists and 
    // the genus G exists in the file of its rank and discriminant.
    r := Rank(G);
    D := Determinant(G);
    if not ExistsLatticeGeneraDataFile(r,D) then return false; end if;
    S := LatticeGenera(LatticeGeneraDatabase(),r,D);
    for L in S do
	if L eq G then return true; end if;
    end for;
    return false;
end function;

function ExistsLatticeGeneraDataFile(r,D)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the file handle for reading.
    filename, dirpath := GeneraFilename(r,D);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function LatticeGeneraDataFile(r,D)
    // Creates the uncompressed file for writing.
    filename, dirpath := GeneraFilename(r,D);
    if System("test -d " * dirpath) ne 0 then
	System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;

