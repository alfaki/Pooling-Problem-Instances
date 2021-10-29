$ontext
    File name: hrspmodel.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for the multi-start alternate heuristic with the Q-formulation.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options 
#optcr=1.e-5, optca=1.e-5, 
limrow=0, limcol=0;

#===============================================================================
# Declare sets and parameters
#===============================================================================
sets lt(i), l(i);
lt(i) = i(i)-s(i); l(i) = i(i)-s(i)-t(i);
parameters Fp(i,j), Yp(s,i); Fp(i,j) = 0; Yp(s,i) = 0;
scalars igap, gap; igap = 1.e-3; gap = 1.e-6; 

# Is there a path between (s,l)
parameter p(i,j);
#===============================================================================
# Compute p(s,i) using the Breadth-first-search (BFS)
#===============================================================================
alias (i,ii,iii), (j,jj), (l,h), (s,ss);
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
positive variables f(i,j), y(s,i);

y.up(s,l) = p(s,l);
f.up(i,j) = min(bu(i),bu(j))*a(i,j);

#===============================================================================
equations obj1, obj2, sflowcaplb1(s), sflowcaplb2(s), sflowcapub1(s), 
          sflowcapub2(s), tflowcaplb1(t), tflowcaplb2(t), ptflowcapub1(i), 
          ptflowcapub2(i), flowpathblnc1(s,i), flowpathblnc2(s,i), 
          qualub1(t,k), qualub2(t,k), propblnc2(i);

#===============================================================================
# Define constraints
#=========================Fixing proportion variables===========================
obj1.. cost =e= sum((i,j)$(a(i,j)>0), c(i,j)*f(i,j));
sflowcaplb1(s)$(bl(s)>0).. sum(j$(a(s,j)>0), f(s,j)) =g= bl(s);
sflowcapub1(s)$(bu(s)<+inf).. sum(j$(a(s,j)>0), f(s,j)) =l= bu(s);
tflowcaplb1(t)$(bl(t)>0).. sum(j$(a(j,t)>0), f(j,t)) =g= bl(t);
ptflowcapub1(lt)$(bu(lt)<+inf).. sum(j$(a(j,lt)>0), f(j,lt)) =l= bu(lt);
flowpathblnc1(s,l)$(p(s,l)>0).. sum(j$(a(l,j)>0), Yp(s,l)*f(l,j)) - 
             f(s,l)$(a(s,l)>0) - sum(h$(p(s,h)*a(h,l)>0), Yp(s,h)*f(h,l)) =e= 0;
qualub1(t,k)$(abs(q(t,k))>0 and abs(q(t,k))<+inf)..
                sum((l,s)$(p(s,l)*a(l,t)>0), (q(s,k) - q(t,k))*Yp(s,l)*f(l,t)) +
                              sum(s$(a(s,t)>0), (q(s,k) - q(t,k))*f(s,t)) =l= 0;
option lp = cplex;
model alty /obj1, sflowcaplb1, sflowcapub1, tflowcaplb1, ptflowcapub1, 
            flowpathblnc1, qualub1/;
alty.solprint = 2;
alty.tolinfeas = igap;
#==========================Fixing flow of f(l,j)================================
obj2.. cost =e= sum((s,j)$(a(s,j)>0), c(s,j)*f(s,j)) +
                                          sum((l,j)$(a(l,j)>0), c(l,j)*Fp(l,j));
sflowcaplb2(s)$(bl(s)>0).. sum(j$(a(s,j)>0), f(s,j)) =g= bl(s);
sflowcapub2(s)$(bu(s)<+inf).. sum(j$(a(s,j)>0), f(s,j)) =l= bu(s);
tflowcaplb2(t)$(bl(t)>0).. sum(s$(a(s,t)>0), f(s,t)) + 
                                           sum(l$(a(l,t)>0), Fp(l,t)) =g= bl(t);
ptflowcapub2(lt)$(bu(lt)<+inf).. sum(s$(a(s,lt)>0), f(s,lt)) + 
                                        sum(l$(a(l,lt)>0), Fp(l,lt)) =l= bu(lt);
flowpathblnc2(s,l)$(p(s,l)>0).. sum(j$(a(l,j)>0), y(s,l)*Fp(l,j)) - 
             f(s,l)$(a(s,l)>0) - sum(h$(p(s,h)*a(h,l)>0), y(s,h)*Fp(h,l)) =e= 0;
qualub2(t,k)$(abs(q(t,k))>0 and abs(q(t,k))<+inf)..
                sum((l,s)$(p(s,l)*a(l,t)>0), (q(s,k) - q(t,k))*y(s,l)*Fp(l,t)) +
                              sum(s$(a(s,t)>0), (q(s,k) - q(t,k))*f(s,t)) =l= 0;
propblnc2(l)..                              sum(s$(p(s,l)>0), y(s,l)) - 1 =e= 0;

model altf /obj2, sflowcaplb2, sflowcapub2, tflowcaplb2, ptflowcapub2, 
            flowpathblnc2, qualub2, propblnc2/;
altf.solprint = 2;
altf.tolinfeas = igap;
#===============================================================================
$set console 
$ifthen set fo $set console msmmodel.log
$elseif %system.filesys% == UNIX $set console /dev/tty
$elseif %system.filesys% == DOS $set console con
$else "%console%." == "." abort "file system not recognized"
$endif
file screen /'%console%'/;
put screen;
put /;
put 'Multi-start Alternate Heuristic'/;
put '========================================='/;
put 'Iter          Time      Feasible Solution'/;
putclose;

scalars converge, starttime, elapsed, p0, solp, soltime; 
p0 = 0; solp = 0; soltime = 0; starttime = jnow;
scalars alt_obj, obj_best, ttime; obj_best = inf; ttime = 1200;
parameter fs(i,j), ys(s,i);
fs(i,j)$(a(i,j)>0) = 0;

repeat(
  execseed = 1+gmillisec(jnow);
  Yp(s,l)$(p(s,l)>0) = uniform(0,1);
  p0 = p0+1;
  repeat(
    f.l(i,j) = 0; cost.l = 0;
    solve alty minimizing cost using lp;
    Fp(l,j) = f.l(l,j);
    y.l(s,l) = 0; f.l(s,j) = 0; cost.l = 0;
    solve altf minimizing cost using lp;
    Fp(s,j) = f.l(s,j);
    converge = (alty.modelstat le 2 and altf.modelstat le 2 and 
                smax((s,l)$(p(s,l)>0), abs(y.l(s,l)-Yp(s,l))) < gap and 
                smax((i,j)$(a(i,j)>0), abs(f.l(i,j)-Fp(i,j))) < gap);
    Yp(s,l) = y.l(s,l);
    elapsed = (jnow - starttime)*24*3600;
  until(converge or elapsed ge ttime));
  if((converge and elapsed le ttime), 
    alt_obj = sum((i,j)$(a(i,j)>0), c(i,j)*f.l(i,j));
    if((alt_obj < obj_best), 
      obj_best = alt_obj;
      fs(i,j)$(a(i,j)>0) = f.l(i,j);
      ys(s,l) = y.l(s,l);
      solp = p0;
      soltime = (jnow - starttime)*24*3600;
      put screen;
      screen.nw = 4;
      screen.nd = 0;
      put p0;
      screen.nw = 7;
      screen.nd = 2;
      put @12 soltime;
      screen.nw = 16;
      screen.nd = 6;
      put @26 obj_best/;
      putclose;        
    );
  );
  elapsed = (jnow - starttime)*24*3600;
until(elapsed ge ttime));

if((elapsed>ttime), elapsed = ttime;);

Fp(i,j) = fs(i,j);
Yp(s,l) = ys(s,l);

put screen;
screen.nw = 16;
put /'========================================='/;
put 'Best feasible solution = ' obj_best /;
screen.nd = 0;
put 'Soltion found at iter  = ' solp /;
put 'Total number of iters  = ' p0 /;
screen.nd = 2;
put 'Soution found at time  = ' soltime /;
put 'Total time in seconds  = ' elapsed /;
put '========================================='/;
putclose;
#============================Print solution information=========================
scalar vars, lcsts;
vars = max(alty.numvar,altf.numvar)-1;
lcsts = max(alty.numequ,altf.numequ)-1;
file line;
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nw = 16;
line.nd = 6;
put_utility line 'msg' / obj_best ' ' soltime ' ' elapsed ' ' solp ' ' 0.0;
line.nd = 0;
put_utility line 'msg' / 1 ' ' p0 ' ' vars ' ' 0 ' ' lcsts ' ' 0;
# First row: best sol (ub), sol time, total time.
# Second row: solstat, num iter, vars, sol iter, lconsts, 
option Fp:6:0:2; display Fp;
option Yp:6:0:2; display Yp;
execute_unload 'sol.gdx', Fp, Yp;
#========================================END====================================