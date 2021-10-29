$ontext
    File name: hybmodel.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the HYB-formulation.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options optcr=1.e-3, limrow=0, limcol=0, reslim=3600;

#===============================================================================
# Declare sets
#===============================================================================
sets lt(i), l(i), l1(i), i1(i), l2(i);
lt(i) = i(i)-s(i); l(i) = i(i)-s(i)-t(i);
alias (l,h), (l1,h1), (l2,h2), (i1,j1);
l1(i) = i(i)-s(i)-t(i);
loop(l,
     l1(h)$(a(l,h)>0) = no;
);
l2(i) = l(i)-l1(i); i1(i) = i(i)-l1(i);

# Is there a path between (s,l)
parameter p(i,j);
#===============================================================================
# Compute p(s,i) using the Breadth-first-search (BFS)
#===============================================================================
alias (i,ii,iii), (j,jj);
scalar u,path,n,mn;
set openlst(i);
set closedlst(i);
parameter val(i);
loop((ii,jj)$(ord(ii)<=ord(jj)),
  n = 1;
  path = 0;
  val(i) = +inf;
  openlst(i) = no;
  closedlst(i) = no;
  openlst(i)$(ord(i) eq ord(ii)) = yes;
  val(i)$(ord(i) eq ord(ii)) = n;
  while((card(openlst)>0 and path eq 0),
    mn = smin(openlst(i), val(i));
    loop(i$openlst(i),
      if((mn eq val(i)),
        u = ord(i);
        val(i) = +inf;
      );
    );
    openlst(i)$(ord(i) eq u) = no;
    if((ord(jj) eq u),
      path = 1;
    else
      closedlst(i)$(ord(i) eq u) = yes;
      loop((iii,j)$(ord(iii) eq u and a(iii,j)>0 and 
                                         not closedlst(j) and not openlst(j)),
        n = n+1;
        val(j) = n;
        openlst(i)$(ord(i) eq ord(j)) = yes;
      );
    );
  );
  p(ii,jj) = path;
);

#===============================================================================
# Declare variables/bounds
#===============================================================================
variables cost, w(i,k), v(k,i,j);
positive variables f(i,j), y(s,i), x(s,i,j);

f.up(i,j1) = min(bu(i), bu(j1))*a(i,j1);
y.up(s,l1) = a(s,l1);
w.lo(l2,k) = smin(s$(p(s,l2)>0), q(s,k));
w.up(l2,k) = smax(s$(p(s,l2)>0), q(s,k));
x.up(s,l1,j) = min(bu(s),bu(l1), bu(j))*a(s,l1)*a(l1,j);

#===============================================================================
# Declare constraints
#===============================================================================
equations obj, sflowcaplb(s), sflowcapub(s), pflowcapub(i), tflowcaplb(t),
          tflowcapub(i), flowpathblnc(i), flowmassblnc(i), qualblnc(i,k),
          propblnc(i), qualub(t,k), rlt1(i,j), rlt2(s,i), commodflowdef(s,i,j),
          flowweight(k,i,j);

#===============================================================================
# Define constraints
#===============================================================================
#-----------------------------Objective function--------------------------------
obj.. cost =e= sum((s,j1)$(a(s,j1)>0), c(s,j1)*f(s,j1)) +
                        sum((s,l1,j)$(a(s,l1)*a(l1,j)>0), c(s,l1)*x(s,l1,j)) +
                                          sum((l,j)$(a(l,j)>0), c(l,j)*f(l,j));
#-------------------------Raw material availabilities---------------------------
sflowcaplb(s)$(bl(s)>0).. sum(j1$(a(s,j1)>0), f(s,j1)) +
                           sum((l1,j)$(a(s,l1)*a(l1,j)>0),x(s,l1,j)) =g= bl(s);
sflowcapub(s)$(bu(s)<+inf).. sum(j1$(a(s,j1)>0), f(s,j1)) +
                           sum((l1,j)$(a(s,l1)*a(l1,j)>0),x(s,l1,j)) =l= bu(s);
#----------------Pool capacities and product demand restrictions----------------
pflowcapub(l)$(bu(l)<+inf).. sum(j$(a(l,j)>0), f(l,j)) =l= bu(l);
tflowcaplb(t)$(bl(t)>0).. sum(j$(a(j,t)>0), f(j,t)) =g= bl(t);
tflowcapub(t)$(bu(t)<+inf).. sum(j$(a(j,t)>0), f(j,t)) =l= bu(t);
#-----------------------Commodity flow balance around pools---------------------
flowpathblnc(l1)..
 sum(j$(a(l1,j)>0), f(l1,j)) - sum((s,j)$(a(s,l1)*a(l1,j)>0), x(s,l1,j)) =e= 0;
#------------------------Flow mass balance around pools-------------------------
flowmassblnc(l2)..
               sum(j$(a(j,l2)>0), f(j,l2)) - sum(j$(a(l2,j)>0), f(l2,j)) =e= 0;
#-------------------Quality specifications balances around pools----------------
qualblnc(l2,k).. sum(s$(a(s,l2)>0), q(s,k)*f(s,l2)) +
                         sum((s,l1)$(a(s,l1)*a(l1,l2)>0), q(s,k)*x(s,l1,l2)) +
        sum(h2$(a(h2,l2)>0), v(k,h2,l2)) - sum(j$(a(l2,j)>0), v(k,l2,j)) =e= 0;
#------------------------Product quality specifications-------------------------
qualub(t,k)$(abs(q(t,k))<+inf).. sum(s$(a(s,t)>0), q(s,k)*f(s,t)) +
                           sum((s,l1)$(a(s,l1)*a(l1,t)>0), q(s,k)*x(s,l1,t)) +
       sum(h2$(a(h2,t)>0), v(k,h2,t)) - q(t,k)*sum(j$(a(j,t)>0), f(j,t)) =l= 0;
#-------------------------Commodity proportion balances-------------------------
propblnc(l1).. sum(s$(a(s,l1)>0), y(s,l1)) - 1 =e= 0;
#---------------------RLT for commodity proportion balances---------------------
rlt1(l1,j)$(a(l1,j)>0).. f(l1,j) - sum(s$(a(s,l1)>0), x(s,l1,j)) =e= 0;
#----------------------------RLT for pool capacities----------------------------
rlt2(s,l1)$(a(s,l1)>0 and bu(l1)<+inf).. sum(j$(a(l1,j)>0), x(s,l1,j)) -
                                                          y(s,l1)*bu(l1) =l= 0;
#---------------------------Commodity flow definition---------------------------
commodflowdef(s,l1,j)$(a(s,l1)*a(l1,j)>0).. x(s,l1,j) - y(s,l1)*f(l1,j) =e= 0;
#----------------------------------Weighted flow--------------------------------
flowweight(k,l2,j)$(a(l2,j)>0).. v(k,l2,j) - w(l2,k)*f(l2,j) =e= 0;

#===============================================================================
# Solve the model
#===============================================================================
option nlp = baron;
model hybmodel /all/;
hybmodel.optfile = 1;
hybmodel.solprint = 2;
hybmodel.workspace = 1500;
solve hybmodel minimizing cost using nlp;
#============================Print solution information=========================
scalar nlts;
nlts = 0;
loop((s,l1,j)$(a(s,l1)*a(l1,j)>0),
  nlts = nlts + 1;
);
loop((k,l2,j)$(a(l2,j)>0),
  nlts = nlts + 1;
);
scalars ae, re;
ae = abs(hybmodel.objest - hybmodel.objval);
re = ae/abs(hybmodel.objest);
file line;
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nd = 6;
line.nw = 18;
put_utility line 'msg' / hybmodel.objval ' ' hybmodel.objest ' ' hybmodel.resusd 
' ' re ' ' ae;
line.nd = 0;
put_utility line 'msg' / hybmodel.solvestat ' ' hybmodel.nodusd ' ' 
(hybmodel.numvar-1) ' ' nlts ' ' (hybmodel.numequ-nlts-1) ' ' nlts;
option f:6:0:2; display f.l;
option y:6:0:2; display y.l;
option w:6:0:2; display w.l;
#========================================END====================================