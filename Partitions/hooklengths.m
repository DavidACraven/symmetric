intrinsic HookLengths(pa::SeqEnum[RngIntElt]) -> SetMulti
{Returns the multiset of hook lengths of the partition pa.}

require IsPartition(pa): "Input must be a partition";

return {*HookLength(pa,i,j):j in [1..pa[i]],i in [1..#pa]*};
end intrinsic;


intrinsic IsBetaSet(X::SetEnum[RngIntElt]) -> BoolElt,SeqEnum
{Returns true and the corresponding partition if X is a beta set, and false otherwise.}

if(Minimum(X) lt 0) then return false,_; end if;

// So now the beta set is of a real partition.
nn:=#X;
P:=[];
for i in [1..#X] do
  m:=Maximum(X); Append(~P,m-nn+1);
  nn-:=1;
  Exclude(~X,m);
end for;
// Finally, delete any trailing zeros.
while P[#P] eq 0 do Prune(~P); if(#P eq 0) then break; end if; end while;
return true,P;
end intrinsic;


intrinsic PartitionToBetaSet(pa::SeqEnum[RngIntElt]) -> SetEnum
{Returns the corresponding 'standard' beta-set to the partition pa. This is the beta-set with no 0.}
require IsPartition(pa):"Input must be a partition";
if(#pa eq 0 or pa[1] eq 0) then return {}; end if;
// Remove trailing zeros
while pa[#pa] eq 0 do Prune(~pa); if(#pa eq 0) then break; end if; end while;
return {pa[i]+#pa-i:i in [1..#pa]};
end intrinsic;


intrinsic BetaSetToPartition(X::SetEnum[RngIntElt]) -> SeqEnum
{Returns the partition corresponding to the beta-set X.}
if X eq {} then return []; end if;
require (Minimum(X) ge 0): "Set is not a beta-set";

// This code is the same as IsBetaSet.
nn:=#X;
P:=[];
for i in [1..#X] do
  m:=Maximum(X); Append(~P,m-nn+1);
  nn-:=1;
  Exclude(~X,m);
end for;
while P[#P] eq 0 do Prune(~P); if(#P eq 0) then break; end if; end while;
return P;
end intrinsic;


intrinsic StandardBetaSet(X::SetEnum[RngIntElt]) -> SetEnum
{Returns the standard beta-set equivalent to X.}
if(X eq {}) then return {}; end if;
require Minimum(X) ge 0: "Input is not a beta-set";
if(#X-1 eq Maximum(X) and 0 in X) then return {}; end if;
for i in [0..#X-1] do
  if i notin X then
    return {x-i:x in X|x gt i};
  end if;
end for;
error "Reached a part of the program StandardBetaSet you shouldn't ever reach.";
return 0;
end intrinsic;


intrinsic AreEquivalent(X::SetEnum[RngIntElt],Y::SetEnum[RngIntElt]) -> BoolElt,SetEnum
{Returns true is the beta-sets X and Y are equivalent, and if so the standard beta-set equivalent to both of them.}
if(X eq Y) then
  return true,StandardBetaSet(X);
elif(#X eq #Y) then
  return false,_;
elif(#X gt #Y) then
  Y2:={i+#X-#Y:i in Y} join {i:i in [0..#X-#Y-1]};
  if(X eq Y2) then
    return true,StandardBetaSet(Y);
  else
    return false,_;
  end if;
else
  X2:={i+#Y-#X:i in X} join {i:i in [0..#Y-#X-1]};
  if(X2 eq Y) then
    return true,StandardBetaSet(X);
  else
    return false,_;
  end if;
end if;
error "Reached a part of the program AreEquivalent you shouldn't ever reach.";
return 0;
end intrinsic;


intrinsic ConjugateBetaSet(X::SetEnum[RngIntElt]) -> SetEnum
{The standard beta-set corresponding to the conjugate partition of the partition corresponding to the beta-set X.}

// This can be sped up.

bool,P:=IsBetaSet(X);
require bool: "Input is not a beta-set";
return PartitionToBetaSet(ConjugatePartition(P));
end intrinsic;


intrinsic PrintAbacus(pa::SeqEnum[RngIntElt],t::RngIntElt) -> MonStgElt
{Prints the t-abacus corresponding to the partition pa.}

require IsPartition(pa) and pa[#pa] gt 0: "Input must be a partition with no zero parts";
X:=PartitionToBetaSet(pa);
str:="";
for i in [1..t] do str cat:="O"; end for; str cat:="\n";
for i in [1..t] do str cat:="-"; end for; str cat:="\n";
for j in [0..(Maximum(X) div t)+1] do
  for i in [0..t-1] do
    if(t*j+i in X) then str cat:="O"; else str cat:="|"; end if;
  end for;
  str cat:="\n";
end for;
return str;
end intrinsic;


intrinsic PrintAbacus(X::SetEnum[RngIntElt],t::RngIntElt) -> MonStgElt
{Prints the t-abacus corresponding to the beta-set X of first-column hook lengths.}

require Minimum(X) gt 0: "beta-set must consist of positive integers";

str:="";
for i in [1..t] do str cat:=" O"; end for; str cat:=" \n";
for i in [1..t] do str cat:="--"; end for; str cat:="-\n";
for j in [0..(Maximum(X) div t)+1] do
  for i in [0..t-1] do
    if(t*j+i in X) then str cat:=" O"; else str cat:=" |"; end if;
  end for;
  str cat:=" \n";
end for;
return str;
end intrinsic;



// Opposite to hook lengths and characters are conjugacy classes. So just put this here as somewhere to calculate it


intrinsic NumberOfSymmetricConjugacyClassSizes(n::RngIntElt) -> RngIntElt
{Returns the cardinality of the set of conjugacy class sizes of the symmetric group of degree n. For n up to 100 this is returned from a lookup table. Otherwise the result is calculated, which can take some time.}

requirege n,1;

CardSymConj:=[1,1,3,4,6,7,11,16,23,30,40,58,69,95,119,151,184,240,297,361,452,554,663,817,980,1177,1402,1665,1995,2346,2774,3259,3837,4466,5222,6057,7061,8159,9450,10917,12533,14408,16570,18958,
21623,24681,28123,32000,36232,41109,46504,52566,59287,66831,75261,84606,95015,106515,119337,133540,149201,166575,185860,207157,230433,256352,284834,316133,350634,388527,430052,475626,525650,580558,
640926,706478,778578,857119,942824,1036585,1138850,1250486,1371920,1504094,1648287,1805142,1975245,2160607,2361739,2579885,2816183,3073490,3351567,3653394,3979420,4333070,4715148,5128925,5576141,6058559];

if n le #CardSymConj then return CardSymConj[n]; end if;
// We now have to calculate it since we have reached the end of our look-up table.

num:=NumberOfPartitions(n);
  cc:={};
  P:=[n];
  for i in [1..num] do 
    ii:=SequenceToSet(P);
    nn:=1;
    for j in ii do
      nn*:=j^Multiplicity(P,j)*Factorial(Multiplicity(P,j));
    end for;
    Include(~cc,nn);
    delete nn; delete ii;
    NextPartition(~P);
  end for;
return #cc;
end intrinsic;


