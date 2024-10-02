import "matrixdatabase.m": ReturnProductFormMatrix;

intrinsic PartitionToGroupElement(pa::SeqEnum[RngIntElt]) -> GrpPermElt
{A permutation of a symmetric group with cycle type pa. Although the name suggests that pa must be a partition, any composition will work.}
require Minimum(pa) ge 0: "No entry of pa may be negative";

sofar:=0;
pe:=[];
for index in [1..#pa] do
  pe cat:=[sofar+i:i in [2..pa[index]]] cat [sofar+1];
  sofar+:=pa[index];
end for;
return Sym(&+pa)!pe;
end intrinsic;  

intrinsic SymmetricCharacterValue(pa::SeqEnum[RngIntElt],pe::SeqEnum[RngIntElt]) -> RngIntElt
{Returns the irreducible character value for the character labelled by the partition pa on a permutation of a symmetric group with cycle type the composition pe.}
return SymmetricCharacterValue(pa,PartitionToGroupElement(pe));
end intrinsic;


intrinsic SymmetricCharacterValues(pa::SeqEnum[RngIntElt],cy::SeqEnum[SeqEnum[RngIntElt]]) -> SeqEnum
{The values of the irreducible character labelled by the partition pa evaluated at the cycle types given by cy. Note that cy is a list of partitions/compositions, and not a list of group elements.}
return [SymmetricCharacterValue(pa,PartitionToGroupElement(i)):i in cy];
end intrinsic;


intrinsic SymmetricSylowCycleTypes(n::RngIntElt,p::RngIntElt) -> SeqEnum
{A list of all possible cycle types of elements in a Sylow p-subgroup of a symmetric group of degree n.}
requirege n,1; requirege p,2;
require IsPrime(p): "p is not a prime number";
pow:=Floor(Log(p,n));
theparts:=Reverse(RestrictedPartitions(n,{p^i:i in [0..pow]}));
return [[i:i in j]:j in theparts]; // I have no idea why you need to do this, but Magma won't accept that theparts is a sequence of sequences of integers.
end intrinsic;


// This function translates the simple pm1 and 0,1 ordering on the characters and classes into one where the linear characters are
// labelled by the restriction of hook partitions to Sylow 2-subgroups. At the moment I cannot see a general rule for how this is
// made, so it is computed by restricting the hook partitions to elements.
function SymmetricSylowTransitionMatrix(n)
if(n notin [4,8,16,32,64,128])  then error "Transition matrix for characters has not been stored for this value of n"; end if;

if(n eq 4) then 
  return PermutationMatrix(Rationals(),Sym(4)!(2,3,4));
elif(n eq 8) then 
  return PermutationMatrix(Rationals(),Sym(8)!(2,5,4,3,7,6,8));
elif(n eq 16) then 
  return PermutationMatrix(Rationals(),Sym(16)!(2,9,4,5,7,11,16)(3,13,6,15,10,12,8));
elif(n eq 32) then 
  return PermutationMatrix(Rationals(),Sym(32)!(2,17,4,9,7,21,16,3,25,6,29,10,23,24,8,5,13,11,31,18,20,12,15,19,28,14,27,30,26,22,32));
elif(n eq 64) then
  return PermutationMatrix(Rationals(),Sym(64)!(2,33,4,17,7,41,16,5,25,11,61,18,39,44,32,3,49,6,57,10,45,24,15,37,28,27,59,58,42,48,8,9,13,
            21,31,35,52,22,63,34,36,20,23,47,40,12,29,19,55,46,56,14,53,30,51,54,62,50,38,60,26,43,64));
elif(n eq 128) then
  return PermutationMatrix(Rationals(),Sym(128)!(2,65,4,33,7,81,16,9,25,21,61,35,103,86,128)(3,97,6,113,10,89,24,29,37,55,91,120,26,85,64)
            (5,49,11,121,18,77,44,63,67,100,38,119,90,88,32)(8,17,13,41,31,69,52,43,127,66,68,36,39,87,96)(12,57,19,109,46,111,78,108,62,99,
            102,118,122,82,80)(14,105,30,101,54,123,114,74,92,56,27,117,58,83,112)(15,73,28,53,59,115,106,94,104,22,125,34,71,84,48)(20,45,
            47,79,76,60,51,107,126,98,70,116,42,95,72)(23,93,40)(50,75,124));
end if;
end function;

// This function gives strings of plus/minus 1s and 0s and 1s, needed for writing down the linear characters of the Sylow subgroup of the symmetric group.
function MakePossibleStrings(n)
pow:=Floor(Log(2,n));
PM1:=[[1],[-1]]; for i in [2..pow] do PM1:=[i cat [j]:i in PM1,j in [1,-1]]; end for;
Z1:=[[0],[1]]; for i in [2..pow] do Z1:=[i cat [j]:i in Z1,j in [0,1]]; end for;
return PM1,Z1;
end function;

intrinsic SymmetricSylow2LinearCharacters(n::RngIntElt) -> Mtrx
{The linear characters of a Sylow 2-subgroup of the symmetric group of degree n, given as a matrix. Note that n must be a power of 2. This function has a certain labelling of the rows and columns. The labelling of the columns is based on the structure of the Sylow subgroup of the symmetric group, and the labelling of the rows is arbitrary//via the hook partitions if n <= 64, and is otherwise arbitrary. (This bound will hopefully change in later versions of the software.)
}

requirege n,2;
require IsEven(n) and IsPrimePower(n): "n must be a power of 2 for now";

PM1,Z1:=MakePossibleStrings(n);
LinChars:=[];
for ii in [1..#PM1] do
  Append(~LinChars,[&*[i[j]^Z1[ii,j]:j in [1..#Z1[1]]]:i in PM1]);
end for;
return Matrix(Rationals(),LinChars);
end intrinsic;

intrinsic SymmetricCharacterSylowRestriction(pa::SeqEnum[RngIntElt],p::RngIntElt) -> SeqEnum
{Returns the restriction of the irreducible character labelled by the partition pa to a Sylow p-subgroup of the symmetric group. The ordering on the elements of a Sylow p-subgroup of the symmetric group is given by the function SymmetricSylowCycleTypes. For hook partitions restricted to the Sylow p-subgroup, use the function SymmetricCharacterHookRestrictions.}
requirege p,2;
require IsPartition(pa): "Input is not a partition";
require IsPrime(p): "p is not a prime";

n:=&+pa;
SylElts:=SymmetricSylowCycleTypes(n,p);
return SymmetricCharacterValues(pa,SylElts);
end intrinsic;


intrinsic SymmetricCharacterHookRestrictions(n::RngIntElt,p::RngIntElt) -> SeqEnum
{Computes (quickly) the restrictions of characters associated to all hook partitions to a Sylow p-subgroup of the symmetric group of degree n.}
requirege n,2;
require IsPrime(p): "p is not a prime";

// Trace of Lambda^k(g) = 1/k sum_{m=1}^k (-1)^{m-1} tr(g^m) tr Lambda^{k-m}(g). Implement this below for exterior powers of the permutation character.

SylTypes:=SymmetricSylowCycleTypes(n,p);
primeMapTuple:=[]; // result of raising an element of SylTypes to the power p.
for i in SylTypes do
  primei:=&cat[[j div p:jj in [1..p]]:j in i|j ne 1] cat [1:j in [1..Multiplicity(i,1)]];
  Append(~primeMapTuple,Position(SylTypes,primei));
end for;
primeMap:=map<[1..#SylTypes]->[1..#SylTypes]|[<i,primeMapTuple[i]>:i in [1..#SylTypes]]>;

powerMaps:=<primeMap^0>;
for m in [2..n div 2] do
  powerTimes:=Valuation(m,p);
  Append(~powerMaps,primeMap^powerTimes);
end for;

PermPowers:=[
[1:i in [1..#SylTypes]], //trivial character
[Multiplicity(i,1):i in SylTypes] // permutationcharacter
];

for k in [2..n div 2] do
  Append(~PermPowers,[1/k*&+[(-1)^(m-1)*PermPowers[2,powerMaps[m](j)]*PermPowers[k-m+1,j]:m in [1..k]]:j in [1..#SylTypes]]);
end for;

HookRestrictions:=[PermPowers[1]];
for i in [2..n div 2] do
  Append(~HookRestrictions,[PermPowers[i,j]-HookRestrictions[i-1,j]:j in [1..#SylTypes]]);
end for;

// Now the rest. If p ne 2 then the higher exterior powers are just the same as the lower ones, otherwise we twist by conjugation.
if(p eq 2) then 
  for i in [n div 2..1 by -1] do Append(~HookRestrictions,SymmetricSylowConjugateCharacter(HookRestrictions[i],n)); end for;
else
  HookRestrictions cat:=Reverse(HookRestrictions);
end if;

return HookRestrictions;

end intrinsic;



intrinsic SymmetricSylowConjugateCharacter(ch::SeqEnum[RngIntElt],n::RngIntElt) -> SeqEnum
{Given a character of a symmetric group of degree n restricted to a Sylow 2-subgroup, returns the conjugate character, i.e., the tensor product of ch with the sign character.}

requirege n,0;
SylTypes:=SymmetricSylowCycleTypes(n,2);
require #SylTypes eq #ch: "Input is not a character of a Sylow 2-subgroup of S_n";
conjchar:=ch;
for ii in [1..#ch] do
  if IsOdd(#SylTypes[ii]) then conjchar[ii]*:=-1; end if;
end for; 
return conjchar;
end intrinsic;


intrinsic SymmetricSylowRestrictionInnerProducts(ch::SeqEnum[RngIntElt],n::RngIntElt) -> SeqEnum
{Returns the list of inner products of the restricted character ch of the symmetric group of degree n with the linear characters according to the labelling by hook partitions. This method currently only works for n = 4,8,16,32,64,128.}
requirege n,1;
require n in [4,8,16,32,64,128]: "At the moment, only 2-powers from 4 up to 128 have been implemented";

FormMat:=ReturnProductFormMatrix(n);
TransMat:=SymmetricSylowTransitionMatrix(n);
LinChars:=SymmetricSylow2LinearCharacters(n);

return Matrix(Rationals(),[ch])*FormMat*LinChars*TransMat^-1*ScalarMatrix(n,1/2^(n-1));
end intrinsic;

intrinsic SymmetricSylowRestrictionInnerProducts(X::SeqEnum[SeqEnum[RngIntElt]],n::RngIntElt) -> SeqEnum
{Returns the list of inner products of the collection X of restricted characters of the symmetric group of degree n with the linear characters according to the labelling by hook partitions. This method currently only works for n = 4,8,16,32,64,128.}
requirege n,1;
require n in [4,8,16,32,64,128]: "At the moment, only 2-powers from 4 up to 128 have been implemented";

FormMat:=ReturnProductFormMatrix(n);
TransMat:=SymmetricSylowTransitionMatrix(n);
LinChars:=SymmetricSylow2LinearCharacters(n);

return Matrix(Rationals(),X)*FormMat*LinChars*TransMat^-1*ScalarMatrix(n,1/2^(n-1));
end intrinsic;
