$ontext
    File name: pmodel.gms
    Author: Mohammed Alfaki, December, 2010.
    GAMS model for 't' heuristic algorithm to the pooling problem.
$offtext

#===============================================================================
# Declare options
#===============================================================================
options optcr=0.001, limrow=0, limcol=0;

#===============================================================================
# Declare sets and parameters
#===============================================================================
sets lt(i), l(i), tau(t), Tp(t);
lt(i) = i(i)-s(i); l(i) = i(i)-s(i)-t(i);
tau(t) = no; Tp(t) = no;
parameters Fp(i,j);
Fp(i,j) = 0;
scalars agap; agap = 0.001;

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
variable cost, w(i,k);
positive variables y(s,i), f(i,j);

w.lo(l,k) = smin(s$(p(s,l)>0),q(s,k));
w.up(l,k) = smax(s$(p(s,l)>0),q(s,k));
y.up(s,l) = a(s,l);
f.up(i,j) = min(bu(i),bu(j))*a(i,j);

#===============================================================================
# Declare constraints
#===============================================================================
equations obj(t), sflowcaplb(s,t), sflowcapub(s,t), tflowcaplb(t), 
          ptflowcapub(i,t), flowmassblnc(i,t), qualubLP(t,k), 
          flowpathblnc(s,i,t), qualub(t,k), qualubTp(t,k), propblnc(i,t), 
          propblncTp(i,t), rlt1(i,t);

#===============================================================================
# Define constraints
#===============================================================================
#-----------------------------Objective function--------------------------------
obj(tau).. cost =e= sum((i,j)$(a(i,j)*p(j,tau)>0), c(i,j)*f(i,j));
#-------------------------Raw material availabilities---------------------------
sflowcaplb(s,tau)$(bl(s)*p(s,tau)>0).. 
                           sum(j$(a(s,j)*p(j,tau)>0), Fp(s,j)+f(s,j)) =g= bl(s);
sflowcapub(s,tau)$(bu(s)<+inf and p(s,tau)>0).. 
                           sum(j$(a(s,j)*p(j,tau)>0), Fp(s,j)+f(s,j)) =l= bu(s);
#----------------Pool capacities and product demand restrictions----------------
tflowcaplb(tau)$(bl(tau)>0).. 
                            sum(j$(a(j,tau)>0), Fp(j,tau)+f(j,tau)) =g= bl(tau);
ptflowcapub(lt,tau)$(bu(lt)<+inf and p(lt,tau)>0).. 
                                sum(j$(a(j,lt)>0), Fp(j,lt)+f(j,lt)) =l= bu(lt);
#------------------------Flow mass balance around pools-------------------------
flowmassblnc(l,tau)$(p(l,tau)>0)..   sum(s$(a(s,l)>0), f(s,l)) - f(l,tau) =e= 0;
#---------------Product quality specifications at tau when p0=0-----------------
qualubLP(tau,k)$(abs(q(tau,k))>0 and abs(q(tau,k))<+inf)..
                              sum(s$(a(s,tau)>0), (q(s,k)-q(tau,k))*f(s,tau)) +
                 sum((s,l)$(a(s,l)*a(l,tau)>0), (q(s,k)-q(tau,k))*f(s,l)) =l= 0;
#-----------------------Commodity flow balance around pools---------------------
flowpathblnc(s,l,tau)$(a(s,l)*a(l,tau)>0).. 
 Fp(s,l)+f(s,l) =e= y(s,l)*(f(l,tau) + sum(Tp$(a(l,Tp)>0), Fp(l,Tp)));
#------------------------Product quality specifications-------------------------
qualub(tau,k)$(abs(q(tau,k))>0 and abs(q(tau,k))<+inf).. 
                              sum(s$(a(s,tau)>0), (q(s,k)-q(tau,k))*f(s,tau)) + 
        sum((s,l)$(a(s,l)*a(l,tau)>0), (q(s,k)-q(tau,k))*y(s,l)*f(l,tau)) =l= 0;
qualubTp(Tp,k)$(abs(q(Tp,k))>0 and abs(q(Tp,k))<+inf).. 
                                sum(s$(a(s,Tp)>0), (q(s,k)-q(Tp,k))*Fp(s,Tp)) + 
          sum((s,l)$(a(s,l)*a(l,Tp)>0), (q(s,k)-q(Tp,k))*y(s,l)*Fp(l,Tp)) =l= 0;
#-------------------------Commodity proportion balances-------------------------
propblnc(l,tau)$(a(l,tau)>0)..              sum(s$(a(s,l)>0), y(s,l)) - 1 =e= 0;
propblncTp(l,Tp)$(a(l,Tp)>0)..              sum(s$(a(s,l)>0), y(s,l)) - 1 =e= 0;
#---------------------RLT for commodity proportion balances---------------------
rlt1(l,tau)$(a(l,tau)>0)..      sum(s$(a(s,l)>0), y(s,l)*f(l,tau)) =e= f(l,tau);
    
#===============================================================================
# Solve the model
#===============================================================================
model hrslp /obj, sflowcaplb, sflowcapub, tflowcaplb, ptflowcapub, flowmassblnc, 
             qualubLP/;
hrslp.solprint = 2;

option nlp = baron;
model hrsnlp /obj, sflowcaplb, sflowcapub, tflowcaplb, ptflowcapub, 
              flowpathblnc, qualub, qualubTp, propblnc, propblncTp, rlt1/;
hrsnlp.solprint = 2;
hrsnlp.tolinfeas = agap;
#===============================================================================
$set console 
$ifthen set fo $set console hrs.log
$elseif %system.filesys% == UNIX $set console /dev/tty
$elseif %system.filesys% == DOS $set console con
$else "%console%." == "." abort "filesys not recognized"
$endif
file screen /'%console%'/;
put screen;
put /;
put 'Model: HRS+MCF, NLP solver: ' system.nlp/;
put '========================================='/;
put 'Iter                    Feasible Solution'/;
putclose;

sets T_diff_Tp(t), tau_p(t);
T_diff_Tp(t) = yes;
alias (T_diff_Tp, T_active);
scalars z_p, obj_best, p0, ttime, starttime, elapsed, mdlstat; 
starttime = jnow; p0 = 0; obj_best = 0; ttime = 3600;
parameters f_p(i,j), Wp(i,k), objp0(t), minobj;
f_p(i,j) = 0; Wp(i,k) = 0; objp0(t) = inf;
scalars tmp, vars, nlts, nlcsts, lcsts; 
vars = 0; nlts = 0; nlcsts = 0; lcsts = 0;

repeat(
  z_p = 0;
  f_p(i,j) = 0;
  put screen;
  put 'Iteration ' (p0+1):>2:0 ':'/;
  putclose;
  if((p0 eq 0), 
	  loop(T_diff_Tp,
      tau(T_diff_Tp) = yes;
      f.l(i,j)$(a(i,j)>0) = 0; cost.l = 0;
      solve hrslp minimizing cost using lp;
      mdlstat = hrslp.modelstat;
      tau(T_diff_Tp) = no;
      put screen;
      put '  Term ' T_diff_Tp.tl:>2:0 ', STAT ' mdlstat:>2:0', obj = ' cost.l/;
      putclose;
      if((mdlstat le 2),
        objp0(T_diff_Tp) = cost.l;
        if((cost.l < z_p),
          z_p = cost.l;
          f_p(i,j)$(a(i,j)>0) = 0;
          f_p(i,j)$(a(i,j)*p(j,T_diff_Tp)>0) = f.l(i,j);
          tau_p(t) = no;
          tau_p(T_diff_Tp) = yes;
          vars = hrslp.numvar-1; nlts = 0;
          lcsts = hrslp.numequ-1; nlcsts = 0;
        );
      );
	  );
  else
    minobj = smin(T_active, objp0(T_active));
	  loop(T_diff_Tp$(objp0(T_diff_Tp) eq minobj),
      tau(T_diff_Tp) = yes;
      f.l(i,j)$(a(i,j)>0) = 0; y.l(s,l)$(p(s,l)>0) = 0; cost.l = 0;
      f.up(i,j) = min(bu(i),bu(j))*a(i,j); y.up(s,l) = p(s,l);
      hrsnlp.reslim = (ttime-(jnow - starttime)*24*3600)/card(T_diff_Tp);
      solve hrsnlp minimizing cost using nlp;
      mdlstat = hrsnlp.modelstat;
      vars = max(vars, hrsnlp.numvar-1); tmp = 0; 
      loop((s,l)$(a(s,l)*a(l,T_diff_Tp)>0), tmp = tmp+1;);  
      nlts = max(nlts, tmp); loop(l$(a(l,T_diff_Tp)>0), tmp = tmp+1;);
      tmp = tmp+card(k); nlcsts = max(nlcsts,tmp); 
      lcsts = max(lcsts, hrsnlp.numequ-nlcsts-1);      
      tau(T_diff_Tp) = no;
      put screen;
      put '  Term ' T_diff_Tp.tl:>2:0 ', STAT ' mdlstat:>2:0', obj = ' cost.l/;
      putclose;
      if((mdlstat le 2),
        z_p = cost.l; 
        f_p(i,j)$(a(i,j)>0) = 0;
        f_p(i,j)$(a(i,j)*p(j,T_diff_Tp)>0) = f.l(i,j);
      else
        z_p = inf;
      );
      tau_p(t) = no;
      tau_p(T_diff_Tp) = yes;
      minobj = inf;
	  );
  );
  p0 = p0+1;
  if((z_p < 0), 
    loop(tau_p, Fp(i,j)$(a(i,j)*p(j,tau_p)>0) = Fp(i,j)+f_p(i,j););
	  Wp(l,k)$(sum(s$(a(s,l)>0), Fp(s,l))> agap) = 
                   sum(s$(a(s,l)>0), q(s,k)*Fp(s,l))/sum(s$(a(s,l)>0), Fp(s,l));
    obj_best = sum((i,j)$(a(i,j)>0), c(i,j)*Fp(i,j));
    Tp(tau_p) = yes;
    put screen;
    screen.nd = 0;
    screen.nw = 4;
    put p0;
    screen.nw = 16;
    screen.nd = 6;
    put @26 obj_best/;
    putclose;
  );
  T_diff_Tp(tau_p) = no;
  elapsed = (jnow - starttime)*24*3600;
until(p0 eq card(t) or elapsed ge ttime));

put screen;
screen.nw = 16;
put /'========================================='/;
put 'Best feasible solution = ' obj_best /;
screen.nd = 2;
put 'Total time in seconds  = ' elapsed /;
put '========================================='/;
putclose;

#============================Print solution information=========================
file line;
put_utility line 'msg' / '#####' ' Solution Summary #####';
line.nd = 6;
line.nw = 16;
put_utility line 'msg' / obj_best ' ' 0.0 ' ' elapsed ' ' 0.0 ' ' 0.0;
line.nd = 0;
put_utility line 'msg' / 1 ' ' p0 ' ' vars ' ' nlts ' ' lcsts ' ' nlcsts;
option Fp:6:0:2; display Fp;
option Wp:6:0:2; display Wp;
#========================================END====================================