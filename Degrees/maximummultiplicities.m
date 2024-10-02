intrinsic MaximumMultiplicityOfSymmetricCharacterDegree(n::RngIntElt) -> RngIntElt
{Returns the largest multiplicity of an irreducible character degree for the symmetric group of degree n. For n up to 115 this is returned from a lookup table. Otherwise the result is calculated, which will take a long time, and more than 500GB of RAM.}

requirege n,1;

// Up to 115. Cannot easily do more without splitting the set.

MaxMults:=[1,2,2,2,2,4,4,2,3,2,4,4,6,6,6,4,8,6,10,6,8,8,12,8,12,12,10,12,22,14,12,12,16,18,30,14,20,26,16,20,22,20,26,25,24,24,
32,16,32,30,26,24,32,32,40,32,34,32,32,34,44,30,44,36,52,34,54,38,56,50,48,44,50,44,58,46,60,48,58,64,72,56,58,66,86,
68,86,78,94,102,84,84,94,80,104,96,104,104,96,104,110,106,112,102,146,104,120,114,132,126,136,126,130,108,144];

if(n le #MaxMults) then return MaxMults[n]; end if;

// We now have to calculate it since we have reached the end of our look-up table.

num:=NumberOfPartitions(n);
P:=[n];
CharDegs:={**};
g:=Sym(n)!1;
for i in [1..num] do
  if(P lt ConjugatePartition(P)) then NextPartition(~P,n); continue i; end if;
  t:=SymmetricCharacterValue(P,g);
  Include(~CharDegs,t); if(not ConjugatePartition(P) eq P) then Include(~CharDegs,t); end if;
  delete t;
  NextPartition(~P,n);
end for;
return Maximum(Multiplicities(CharDegs));

end intrinsic;

intrinsic NumberOfIrreducibleSymmetricCharacterDegrees(n::RngIntElt) -> RngIntElt
{Returns the cardinality of the set of irreducible character degrees of the symmetric group of degree n. For n up to 115 this is returned from a lookup table. Otherwise the result is calculated, which will take a long time, and more than 500GB of RAM.}

requirege n,1;

// Up to 115. Cannot easily do more without splitting the set.

CardSymChar:=[1,1,2,3,4,5,7,12,15,22,28,38,45,52,81,107,130,179,194,280,348,438,502,693,848,1037,1274,1594,1847,2473,2851,3652,4271,
5137,6140,7995,9103,11046,12978,16216,18348,23153,26239,31880,37582,45144,51469,63571,71910,86693,100776,121305,136541,164954,186709,
224614,257334,303932,343577,414191,466517,549489,627545,740341,832921,986960,1116377,1304731,1472704,1723474,1945317,2289555,2567089,
2976885,3369079,3925229,4392363,5109080,5742421,6638468,7472779,8611544,9630984,11144053,12469585,14345342,16123006,18511428,20616477,
23602145,26481657,30305882,33857237,38663957,43083318,49291288,54930417,62398576,69705598,79275230,88301249,100316970,111786442,
126468513,140532749,159604333,177457734,200826601,223135990,250911575,279621935,315542590,349844381,393774500,437208361];

if n le #CardSymChar then return CardSymChar[n]; end if;
// We now have to calculate it since we have reached the end of our look-up table.
num:=NumberOfPartitions(n);
P:=[n];
CharDegs:={1};
g:=Sym(n)!1;
for i in [1..num-2] do
  NextPartition(~P,n);
  if P lt ConjugatePartition(P) then continue i; end if;
  Include(~CharDegs,SymmetricCharacterValue(P,g));
end for;
return #CharDegs;
end intrinsic;

intrinsic AverageMultiplicityOfSymmetricCharacterDegree(n::RngIntElt:AsRational) -> .
{Returns the average multiplicity of an irreducible character degree of the symmetric group of degree n. If the parameter AsRational is set to be true, a rational number is returned. Otherwise a real number is returned. For n up to 115 this is returned from a lookup table. Otherwise the result is calculated, which will take a long time, and more than 500GB of RAM.}

requirege n,1;
require Type(AsRational) eq BoolElt: "Parameter AsRational is not a Boolean";
n1:=NumberOfIrreducibleSymmetricCharacterDegrees(n);
n2:=NumberOfPartitions(n);
if AsRational then
  return n2/n1;
else
  return n2/n1*1.0;
end if;

end intrinsic;

intrinsic MaximumMultiplicityOfSymmetricCharacterDegreeExceeds(n::RngIntElt,d::RngIntElt:IgnoreSelfConjugatePartitions:=false) -> BoolElt
{Returns true if the maximum multiplicity of an irreducible character degree of the symmetric group of degree n exceeds d. This is checked with a lookup table for n at most 115 and by constructing enough character degrees to decide on the truth of the question if n is larger. If the parameter IgnoreSelfConjugatePartitions, default false, is set to true, only partitions that are not self-conjugate are considered, for applications to alternating groups.}

requirege n,1;
requirege d,1;

// Deal with the case where we ignore self-conjugate partitions first.
if(IgnoreSelfConjugatePartitions) then
  num:=NumberOfPartitions(n);
  P:=[n];
  CharDegs:={**};
  g:=Sym(n)!1;
  for i in [1..num] do
    if(P le ConjugatePartition(P)) then P:=NextPartition(P,n); continue i; end if; // Use le here to exclude P=ConjugatePartition(P).
    t:=SymmetricCharacterValue(P,g);
    Include(~CharDegs,t);
    if(Multiplicity(CharDegs,t) gt d/2) then return true; end if; // can use d/2 here because we are only considering not self-conjugate partitions, so every one is doubled.
    delete t;
    P:=NextPartition(P,n);
  end for;
  return false;
end if;

// Now the general case. For n<115 we can use the known maximal multiplicity.
if(n le 115) then return MaximumMultiplicityOfSymmetricCharacterDegree(n) gt d; end if;

// So now we have to check, since n is large
num:=NumberOfPartitions(n);
P:=[n];
CharDegs:={**};
g:=Sym(n)!1;
for i in [1..num] do
  if(P lt ConjugatePartition(P)) then P:=NextPartition(P,n); continue i; end if;
  t:=SymmetricCharacterValue(P,g);
  Include(~CharDegs,t); if(not ConjugatePartition(P) eq P) then Include(~CharDegs,t); end if;
  if(Multiplicity(CharDegs,t) gt d) then return true; end if;
  delete t;
  P:=NextPartition(P,n);
end for;
return false;
end intrinsic;
