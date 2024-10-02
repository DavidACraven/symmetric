declare type InfPart[RngIntElt];
declare attributes InfPart: UnderlyingPartition, Period, MissingHookLengths;

intrinsic InfinityPartition(pa::SeqEnum[RngIntElt],p::RngIntElt) -> InfPart
{Given a partition pa of at most p parts, and an integer p, construct the corresponding infinity-partition.}
requirege p,1;
require IsPartition(pa): "Input is not a partition";
require #pa le p: "Partition has too many rows";

IX:=New(InfPart);
IX`Period:=p;
Y:=pa;
while #Y lt p do Append(~Y,0); end while;
if(Y[p] ne 0) then Y:=[i-Y[p]:i in Y]; end if;
IX`UnderlyingPartition:=Y;
return IX;
end intrinsic;

intrinsic Print(X::InfPart)
{Print X}
printf "Infinity-partition of period %o\n",X`Period;
printf "Leading edge = %o",X`UnderlyingPartition;
end intrinsic;

intrinsic 'eq'(X::InfPart,Y::InfPart) -> BoolElt
{return true if X and Y are equal infinity-partitions.}
return X`Period eq Y`Period and X`UnderlyingPartition eq Y`UnderlyingPartition;
end intrinsic;


intrinsic MissingHookLengths(X::InfPart) -> SetMulti
{The missing hook lengths of the infinity-partition X.}
if assigned X`MissingHookLengths then return X`MissingHookLengths; end if;

MHL:={*X`UnderlyingPartition[i]-X`UnderlyingPartition[j]-i+j:i,j in [1..X`Period]|i lt j*};
X`MissingHookLengths:=MHL;
return MHL;
end intrinsic;


intrinsic SplinteredInfinityPartition(X::InfPart) -> InfPart
{The splintered infinity-partition corresponding to X.}
Y:=New(InfPart);
Y`Period:=X`Period;
Y`UnderlyingPartition:=[X`UnderlyingPartition[1]-X`UnderlyingPartition[i]:i in Reverse([1..X`Period])];
if assigned X`MissingHookLengths then Y`MissingHookLengths:=X`MissingHookLengths; end if;
return Y;
end intrinsic;


intrinsic IsCluster(X::SetEnum[InfPart]) -> BoolElt
{Returns true if the set X of infinity-partitions all have the same missing hook lengths.}
return #{MissingHookLengths(i):i in X} eq 1;
end intrinsic;
intrinsic IsCluster(X::SeqEnum[InfPart]) -> BoolElt
{Returns true if the set X of infinity-partitions all have the same missing hook lengths.}
return #{MissingHookLengths(i):i in X} eq 1;
end intrinsic;

