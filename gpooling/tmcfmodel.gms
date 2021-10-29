$ontext
    File name: tmcfmodel.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the tMCF-formulation.
$offtext

#===============================================================================
# Declare options
#===============================================================================
#options optcr=1.e-3, limrow=0, limcol=0, reslim=3600;
options optcr=1.e-9, optca=1.e-6, limrow=0, limcol=0, reslim=3600;

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
positive variables f(i,j), y(i,t), x(j,i,t);

f.up(i,j) = min(bu(i),bu(j))*a(i,j);
y.up(l,t) = p(l,t);
x.up(j,l,t) = min(bu(j),bu(l),bu(j))*a(j,l)*p(l,t);

#===============================================================================
# Declare constraints
#===============================================================================
equations obj, sflowcaplb(s), sflowcapub(s), tflowcaplb(t), ptflowcapub(i),
          flowpathblnc(j,t), qualub(t,k), propblnc(i), rlt1(j,i), rlt2(j,t),
          commodflowdef(j,i,t);

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
flowpathblnc(l,t)$(p(l,t)>0).. sum(j$(a(j,l)>0), x(j,l,t)) - f(l,t)$(a(l,t)>0) -
                                       sum(h$(a(l,h)*p(h,t)>0), x(l,h,t)) =e= 0;
#------------------------Product quality specifications-------------------------
qualub(t,k)$(abs(q(t,k))>0 and abs(q(t,k))<+inf)..
                     sum((l,s)$(a(s,l)*p(l,t)>0), (q(s,k) - q(t,k))*x(s,l,t)) +
                              sum(s$(a(s,t)>0), (q(s,k) - q(t,k))*f(s,t)) =l= 0;
#-------------------------Commodity proportion balances-------------------------
propblnc(l).. sum(t$(p(l,t)>0), y(l,t)) - 1 =e= 0;
#---------------------RLT for commodity proportion balances---------------------
rlt1(j,l)$(a(j,l)>0).. sum(t$(p(l,t)>0), x(j,l,t)) - f(j,l) =e= 0;
#----------------------------RLT for pool capacities----------------------------
rlt2(l,t)$(p(l,t)>0 and bu(l)<+inf)..
                               sum(j$(a(j,l)>0), x(j,l,t)) - y(l,t)*bu(l) =l= 0;
#---------------------------Commodity flow definition---------------------------
commodflowdef(j,l,t)$(a(j,l)*p(l,t)>0).. x(j,l,t) - f(j,l)*y(l,t) =e= 0;

#===============================================================================
# Solve the model
#===============================================================================
option nlp = baron;
model tmcfmodel /all/;
$onecho > baron.opt
maxiter -1
rlt1.equclass('*','*') 1
rlt2.equclass('*','*') 1
$offecho
tmcfmodel.optfile = 1;
tmcfmodel.solprint = 2;
tmcfmodel.workspace = 1500;
solve tmcfmodel minimizing cost using nlp;
#============================Print solution information=========================
scalar nlts;
nlts = 0;
loop((j,l,t)$(a(j,l)*p(l,t)>0),
  nlts = nlts + 1;
);
scalars ae, re;
ae = abs(tmcfmodel.objest - tmcfmodel.objval);
re = ae/abs(tmcfmodel.objest);
file line;
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nd = 6;
line.nw = 18;
put_utility line 'msg' / tmcfmodel.objval ' ' tmcfmodel.objest ' ' 
tmcfmodel.resusd ' ' re ' ' ae;
line.nd = 0;
put_utility line 'msg' / tmcfmodel.solvestat ' ' tmcfmodel.nodusd ' ' 
(tmcfmodel.numvar-1) ' ' nlts ' ' (tmcfmodel.numequ-nlts-1) ' ' nlts;
option f:6:0:2; display f.l;
option y:6:0:2; display y.l;
#========================================END====================================