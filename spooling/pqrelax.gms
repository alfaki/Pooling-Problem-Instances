$ontext
    File name: pqrelax.gms.
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the PQ-relaxation.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options optcr=1.e-9, limrow=0, limcol=0, iterlim=1.e9, reslim=1.e9;

#===============================================================================
# Declare sets
#===============================================================================
set l(i); l(i) = i(i)-s(i)-t(i);

#===============================================================================
# Declare variables/bounds
#===============================================================================
variable cost;
positive variables y(s,i), f(i,t), x(s,i,t);

y.up(s,i) = a(s,i);
f.up(i,t) = min(bu(i),bu(t))*a(i,t);
x.up(s,i,t) = min(bu(s),bu(i),bu(t))*a(s,i)*a(i,t);

#===============================================================================
# Declare constraints
#===============================================================================
equations obj, sflowcaplb(s), sflowcapub(s), pflowcapub(i), tflowcaplb(t), 
          tflowcapub(t), qualub(t,k), propblnc(i), rlt1(i,t), rlt2(s,j), 
          vexlb(s,i,t), vexub(s,i,t), cavlb(s,i,t), cavub(s,i,t);

#===============================================================================
# Define constraints
#===============================================================================
#-----------------------------Objective function--------------------------------
obj.. cost =e= sum((s,l,t)$(a(s,l)*a(l,t)>0),(c(s,l) + c(l,t))*x(s,l,t))
                                        + sum((s,t)$(a(s,t)>0), c(s,t)*f(s,t));
#-------------------------Raw material availabilities---------------------------
sflowcaplb(s)$(bl(s)>0).. sum((l,t)$(a(s,l)*a(l,t)>0), x(s,l,t)) + 
                                           sum(t$(a(s,t)>0), f(s,t)) =g= bl(s);
sflowcapub(s)$(bu(s)<+inf).. sum((l,t)$(a(s,l)*a(l,t)>0), x(s,l,t)) +
                                           sum(t$(a(s,t)>0), f(s,t)) =l= bu(s);
#-------------------------------Pool capacities---------------------------------
pflowcapub(l)$(bu(l)<+inf).. 
                     sum((s,t)$(a(s,l)*a(l,t)>0), x(s,l,t)) =l= bu(l);
#-------------------------Product demand restrictions---------------------------
tflowcaplb(t)$(bl(t)>0).. sum((s,l)$(a(s,l)*a(l,t)>0), x(s,l,t)) + 
                                           sum(s$(a(s,t)>0), f(s,t)) =g= bl(t);
tflowcapub(t)$(bu(t)<+inf).. sum((s,l)$(a(s,l)*a(l,t)>0), x(s,l,t)) + 
                                           sum(s$(a(s,t)>0), f(s,t)) =l= bu(t);
#------------------------Product quality specifications-------------------------
qualub(t,k)$(abs(q(t,k))>0 and abs(q(t,k))<+inf).. 
              sum((l,s)$(a(s,l)*a(l,t)>0), (q(s,k) - q(t,k))*x(s,l,t)) + 
                             sum(s$(a(s,t)>0), (q(s,k) - q(t,k))*f(s,t)) =l= 0;
#------------------------------Proportion balances------------------------------
propblnc(l).. sum(s$(a(s,l)>0), y(s,l)) =e= 1;
#--------------------------RLT for proportion balances--------------------------
rlt1(l,t)$(a(l,t)>0).. sum(s$(a(s,l)>0), x(s,l,t)) =e= f(l,t);
#----------------------------RLT for pool capacities----------------------------
rlt2(s,l)$(a(s,l)*bu(l)<+inf).. 
                                  sum(t$(a(l,t)>0), x(s,l,t)) =l= bu(l)*y(s,l);
#---------------Convex/concave envelopes of x(s,l,t) = y(s,l)*f(l,t)------------
vexlb(s,l,t)$(a(s,l)>0 and a(l,t)>0).. x(s,l,t) =g= y.lo(s,l)*f(l,t) +
                                        y(s,l)*f.lo(l,t) - y.lo(s,l)*f.lo(l,t); 
vexub(s,l,t)$(a(s,l)>0 and a(l,t)>0).. x(s,l,t) =g= y.up(s,l)*f(l,t) +
                                        y(s,l)*f.up(l,t) - y.up(s,l)*f.up(l,t);
cavlb(s,l,t)$(a(s,l)>0 and a(l,t)>0).. x(s,l,t) =l= y.lo(s,l)*f(l,t) +
                                        y(s,l)*f.up(l,t) - y.lo(s,l)*f.up(l,t);
cavub(s,l,t)$(a(s,l)>0 and a(l,t)>0).. x(s,l,t) =l= y.up(s,l)*f(l,t) +
                                        y(s,l)*f.lo(l,t) - y.up(s,l)*f.lo(l,t);

#===============================================================================
# Solving the model
#===============================================================================
option lp = cplex;
model pqrelax /all/;
pqrelax.solprint = 2;
solve pqrelax minimizing cost using lp;
#============================Print solution information=========================
scalars ae, re;
ae = abs(pqrelax.objval - pqrelax.objval);
re = ae/abs(pqrelax.objval);
file line; 
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nd = 6;
line.nw = 18;
put_utility line 'msg' / pqrelax.objval ' ' pqrelax.objval ' ' pqrelax.resusd 
' ' re ' ' ae;
line.nd = 0;
put_utility line 'msg' / pqrelax.solvestat ' ' pqrelax.iterusd ' ' 
(pqrelax.numvar-1) ' ' 0 ' ' (pqrelax.numequ-1) ' ' 0;
option f:6:0:2; display f.l;
option y:6:0:2; display y.l;
#========================================END====================================