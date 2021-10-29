$ontext
    File name: mcfmodel.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the MCF-formulation.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options optcr=1.e-3, limrow=0, limcol=0, reslim=3600;

#===============================================================================
# Declare sets
#===============================================================================
sets lt(i), l(i);
lt(i) = i(i)-s(i); l(i) = i(i)-s(i)-t(i);

# Is there a path between (s,l)
parameter p(i,j);
#===============================================================================
# Compute p(s,i) using the Breadth-first-search (BFS)
#===============================================================================
alias (i,ii,iii), (j,jj), (l,h);
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
variable cost;
positive variables f(i,j), y(s,i), x(s,i,j);

f.up(i,j) = min(bu(i),bu(j))*a(i,j);
y.up(s,l) = p(s,l);
x.up(s,l,j) = min(bu(s),bu(l),bu(j))*p(s,l)*a(l,j);

#===============================================================================
# Declare constraints
#===============================================================================
equations obj, sflowcaplb(s), sflowcapub(s), tflowcaplb(t), ptflowcapub(i),
          flowpathblnc(s,i), qualub(t,k), propblnc(i), rlt1(i,j), rlt2(s,i),
          commodflowdef(s,i,j);

#===============================================================================
# Define constraints
#===============================================================================
#-----------------------------Objective function--------------------------------
obj.. cost =e= sum((i,j)$(a(i,j)>0), c(i,j)*f(i,j));
#-------------------------Raw material availabilities---------------------------
sflowcaplb(s)$(bl(s)>0).. sum(j$(a(s,j)>0), f(s,j)) =g= bl(s);
sflowcapub(s)$(bu(s)<+inf).. sum(j$(a(s,j)>0), f(s,j)) =l= bu(s);
#----------------Pool capacities and product demand restrictions----------------
tflowcaplb(t)$(bl(t)>0).. sum(j$(a(j,t)>0), f(j,t)) =g= bl(t);
ptflowcapub(lt)$(bu(lt)<+inf).. sum(j$(a(j,lt)>0), f(j,lt)) =l= bu(lt);
#-----------------------Commodity flow balance around pools---------------------
flowpathblnc(s,l)$(p(s,l)>0).. sum(j$(a(l,j)>0), x(s,l,j)) - f(s,l)$(a(s,l)>0) -
                                       sum(h$(p(s,h)*a(h,l)>0), x(s,h,l)) =e= 0;
#------------------------Product quality specifications-------------------------
qualub(t,k)$(abs(q(t,k))>0 and abs(q(t,k))<+inf)..
                     sum((l,s)$(p(s,l)*a(l,t)>0), (q(s,k) - q(t,k))*x(s,l,t)) +
                              sum(s$(a(s,t)>0), (q(s,k) - q(t,k))*f(s,t)) =l= 0;
#-------------------------Commodity proportion balances-------------------------
propblnc(l).. sum(s$(p(s,l)>0), y(s,l)) - 1 =e= 0;
#---------------------RLT for commodity proportion balances---------------------
rlt1(l,j)$(a(l,j)>0).. sum(s$(p(s,l)>0), x(s,l,j)) - f(l,j) =e= 0;
#----------------------------RLT for pool capacities----------------------------
rlt2(s,l)$(p(s,l)>0 and bu(l)<+inf)..
                               sum(j$(a(l,j)>0), x(s,l,j)) - y(s,l)*bu(l) =l= 0;
#---------------------------Commodity flow definition---------------------------
commodflowdef(s,l,j)$(p(s,l)*a(l,j)>0).. x(s,l,j) - y(s,l)*f(l,j) =e= 0;

#===============================================================================
# Solve the model
#===============================================================================
option nlp = baron;
model mcfmodel /all/;
$onecho > baron.opt
maxiter -1
rlt1.equclass('*','*') 1
rlt2.equclass('*','*') 1
$offecho
mcfmodel.optfile = 1;
mcfmodel.solprint = 2;
mcfmodel.workspace = 1500;
solve mcfmodel minimizing cost using nlp;
#============================Print solution information=========================
scalar nlts;
nlts = 0;
loop((s,l,j)$(p(s,l)*a(l,j)>0),
  nlts = nlts + 1;
);
scalars ae, re;
ae = abs(mcfmodel.objest - mcfmodel.objval);
re = ae/abs(mcfmodel.objest);
file line;
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nd = 6;
line.nw = 18;
put_utility line 'msg' / mcfmodel.objval ' ' mcfmodel.objest ' ' mcfmodel.resusd 
' ' re ' ' ae;
line.nd = 0;
put_utility line 'msg' / mcfmodel.solvestat ' ' mcfmodel.nodusd ' ' 
(mcfmodel.numvar-1) ' ' nlts ' ' (mcfmodel.numequ-nlts-1) ' ' nlts;
option f:6:0:2; display f.l;
option y:6:0:2; display y.l;
#========================================END====================================