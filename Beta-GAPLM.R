##This model was implemented in GAMLSS package
library(gamlss)
library(purrr)
library(betareg)
library(Matrix)
library(simplexreg)
library(ggplot2)
library(matrixcalc)
library(GoFKernel)
library(pracma)
library(cubature)
library(rootSolve)
library(aod)
library(qqplotr)
library(MASS)
library(ggrepel)


####################################################################################
######################### Estimation process #######################################
####################################################################################


dBET<-function(y, mu=0.5, sigma=1, log = FALSE){
  if(any(0.99999<mu & mu<1.000001)){
    mu[which(0.99999<mu & mu<1.000001)]=0.9999
  }
  if (any(mu <= 0)) 
    stop(paste("mu must be between 0 and 1", "\n",""))
  if(any(sigma <= 0)) stop(paste("sigma must be positive","\n",""))
  #if(any(mu <= 0)|any(mu >= 1)) stop(paste("mu must be between 0 and 1","\n",""))
  if (any(y <= 0) | any(y >= 1)) stop(paste("y must be between 0 and 1", "\n",""))
  fy<-dbeta(y,shape1=mu*sigma, shape2=(1-mu)*sigma,ncp=0, log = log)
  fy
}

pBET<- function(q, mu=0.5, sigma=1, lower.tail = TRUE, log.p = FALSE){
  if(any(sigma <= 0)) stop(paste("sigma must be positive","\n",""))
  if(any(mu <= 0)|any(mu >= 1)) stop(paste("mu must be between 0 and 1","\n",""))
  if (any(q <= 0) | any(q >= 1)) stop(paste("y must be between 0 and 1", "\n",""))
  cdf<-pbeta(q,shape1=mu*sigma, shape2=(1-mu)*sigma,ncp=0, lower.tail = lower.tail, 
                   log.p = log.p)
  cdf
}

qBET<-function(p, mu=0.5, sigma=1, lower.tail = TRUE, log.p = FALSE){
  if(any(sigma <= 0)) stop(paste("sigma must be positive","\n",""))
  if(any(mu <= 0)|any(mu >= 1)) stop(paste("mu must be between 0 and 1","\n",""))
  if(any(p <= 0)|any(p >= 1)) stop(paste("p must be between 0 and 1","\n",""))
  q<-qbeta(p,shape1=mu*sigma, shape2=(1-mu)*sigma,ncp=0, lower.tail = lower.tail, 
                        log.p = log.p)
  q
}

rBET<-function(n,mu=0.5,sigma=1){
  if(any(sigma<= 0)) stop(paste("sigma must be positive","\n",""))
  if(any(mu <= 0)|any(mu >= 1)) stop(paste("mu must be between 0 and 1","\n",""))
  if (any(n <= 0)) 
    stop(paste("n must be a positive integer", "\n",""))
  r<-rbeta(n,shape1=mu*sigma, shape2=(1-mu)*sigma)
  while(any(r>0.99999)){
    r[which(r>0.99999)]=rbeta(length(which(r>0.99999)),
                              mu[which(r>0.99999)]*phi[which(r>0.99999)],
                              (1-mu[which(r>0.99999)])*phi[which(r>0.99999)])
  }
  r
}


BET<-function (mu.link = "logit", sigma.link = "log") 
{
  mstats <- checklink("mu.link", "Betar", substitute(mu.link), 
                      c("logit", "probit", "cloglog", "cauchit", "log", "own"))
  dstats <- checklink("sigma.link", "Betar", substitute(sigma.link), 
                      c("log", "sqrt", "1/x^2"))
  structure(list(family = c("BET", "Betar"), parameters = list(mu = TRUE,sigma = TRUE), 
                 nopar = 2, 
                 type = "Continuous", 
                 mu.link = as.character(substitute(mu.link)), 
                 sigma.link = as.character(substitute(sigma.link)), 
                 mu.linkfun = mstats$linkfun, 
                 sigma.linkfun = dstats$linkfun, 
                 mu.linkinv = mstats$linkinv, 
                 sigma.linkinv = dstats$linkinv, 
                 mu.dr = mstats$mu.eta, 
                 sigma.dr = dstats$mu.eta, 
                 dldm = function(y,mu, sigma) {
                   a <- (1-mu)*sigma
                   b <- mu*sigma
                   dldm <- sigma*(log(y)-log(1-y)+digamma(a)-digamma(b))
                   dldm
                 }, 
                 d2ldm2 = function(mu, sigma) {
                   a <-(1-mu)*sigma
                   b <-mu*sigma
                   d2ldm2 <- -(sigma^2*(trigamma(b)+trigamma(a)))
                   d2ldm2
                 }, 
                 dldd = function(y, mu, sigma) {
                   a <- (1-mu)*sigma
                   b <- mu*sigma
                   dldd <-  mu*(log(y)-log(1-y)+digamma(a)-digamma(b))+log(1-y)-digamma(a)+digamma(sigma)
                   dldd
                 }, 
                 d2ldd2 = function(mu, sigma) {
                   a <- mu*sigma
                   b <- (1-mu)*sigma
                   d2ldd2 <- -(trigamma(a)*mu^2+trigamma(b)*(1-mu)^2-trigamma(sigma))
                   d2ldd2
                 }, 
                 d2ldmdd = function(mu, sigma) {
                   a <- mu*sigma
                   b <- (1-mu)*sigma
                   d2ldmdd <- -(sigma*trigamma(a)*mu-sigma*trigamma(b)*(1-mu))
                   d2ldmdd
                 }, 
                 G.dev.incr = function(y, mu, sigma, w, ...) -2 * dBET(y,mu, sigma, log = TRUE),
                 rqres = expression(rqres(pfun = "pBET", type = "Continuous", y = y, mu = mu, sigma = sigma)), 
                 mu.initial = expression({mu <- (y + mean(y))/2}), 
                 sigma.initial = expression({sigma <- rep(0.5, length(y))}), 
                 mu.valid = function(mu) all(mu > 0 & mu < 1), 
                 sigma.valid = function(sigma) all(sigma > 0),
                 y.valid = function(y) all(y > 0 & y < 1), 
                 mean = function(mu, sigma) mu, 
                 variance = function(mu, sigma) mu * (1 - mu)/(1+sigma)), 
            class = c("gamlss.family", "family"))
}

loglog  <- function()
{
  linkfun <- function(mu) { -log(-log(mu))} 
  linkinv <- function(eta) { 
    thresh <- log(-log(.Machine$double.eps))
    eta <- pmin(thresh, pmax(eta, -thresh))
    exp(-exp(-eta))}
  mu.eta <- function(eta) pmax(exp(-eta) * exp(-exp(-eta)), 
                               .Machine$double.eps)
  valideta <- function(eta) TRUE
  link <- "loglog"
  structure(list(linkfun = linkfun, linkinv = linkinv, mu.eta = mu.eta, 
                 valideta = valideta, name = link), class = "link-gamlss")
}



####################################################################################
########################### Diagnostic tools #######################################
####################################################################################



### Information Criteria

criteria=function(mod){
  gamms=list(NULL)
  nq=ncol(mod$mu.s)
  p=ncol(mod$mu.x)-ncol(mod$mu.s)
  for(i in 1:nq){
    gamms[[i]]=mod$mu.coefSmo[[i]][1]$coef
  }
  gamm=Reduce("rbind",gamms)
  Ds<-list(NULL)
  for (i in 1:nq){
    ajus=pb(mod$mu.x[,which(colnames(mod$mu.x) %in% colnames(mod$mu.s)[i])],
            lambda = mod$mu.lambda[i],
            control=pb.control(inter=length(mod$mu.coefSmo[[1]]$knots)-3))
    Ds[[i]]=t(attr(ajus,"D"))%*%attr(ajus,"D")*mod$mu.lambda[i]/2
  }
  D=bdiag(Ds)
  k=mod$df.fit
  HQIC=-2*(as.numeric(logLik(mod))-t(gamm)%*%D%*%gamm)+2*k*log(log(mod$N))
  AIC=-2*(as.numeric(logLik(mod))-t(gamm)%*%D%*%gamm)+2*k
  BIC=-2*(as.numeric(logLik(mod))-t(gamm)%*%D%*%gamm)+log(mod$N)*k
  AICC=AIC+2*k*(k+1)/(mod$N-k-1)
  SABIC=-2*(as.numeric(logLik(mod))-t(gamm)%*%D%*%gamm)+k*log((mod$N+2)/24)
  criteria<-list("AIC"=AIC,"BIC"=BIC,"AICC"=AICC,"HQIC"=HQIC,"SABIC"=SABIC)
}

criteria(mod)$AIC;criteria(mod)$AICC;criteria(mod)$BIC;criteria(mod)$SABIC;criteria(mod)$HQIC


### Quantile-quantile plot of the residuals
plotres=function(mod){
  smp <- data.frame(norm = mod$residuals)
  s1<-ggplot(data = smp, mapping = aes(sample = norm))  +
    stat_qq_band(conf = 0.95) +
    stat_qq_line() +
    stat_qq_point() +
    labs(x = "Theoretical Quantiles", y = "Quantile Residuals") +
    theme(
      panel.border = element_blank(),
      panel.grid.major = element_blank(),
      panel.grid.minor = element_blank(),
      panel.background = element_blank(),
      axis.line = element_line(colour = "grey"),
      text=element_text(size=20,family="serif")
    )  
  print(s1)
}



gmu=function(mod){
  x = mod$mu.link
  mu=mod$mu.fv
  
  if(x=="logit"){
    dmu=(1/mu+1/(1-mu))^(-1)
    d2mu2=-1/mu^2+1/(1-mu)^2
  }
  if(x=="cloglog"){
    dmu=(1/(log(1-mu)*(mu-1)))^(-1)
    d2mu2=-(log(1-mu)+1)/(log(1-mu)*(mu-1))^2
  }
  if(x=="loglog"){
    dmu=(-1/(mu*log(mu)))^(-1)
    d2mu2=(log(mu)+1)/(mu^2*log(mu)^2)
  }
  if(x=="cauchit"){
    dmu=(pi/(cos(pi*(mu-1/2)))^2)^(-1)
    d2mu2=(2*pi^2*sin(pi*(mu-1/2)))/(cos(pi*(mu-1/2)))^3
  }
  if(x=="probit"){
    dmu=(1/dnorm(qnorm(mu)))^(-1)
    d2mu2=-dnorm(qnorm(mu))*(-qnorm(mu))/(dnorm(qnorm(mu)))^3
  }
  ddmu<-list("dmu"=dmu,"d2mu2"=d2mu2)
}
gphi=function(mod){
  x=mod$phi.link
  phi=mod$phi.fv
  if(x=="log"){
    dphi=(1/phi)^(-1)
    d2phi2=-1/phi^2
  }
  if(x=="1/x^2"){
    dphi=(-(2/phi^3))^(-1)
    d2phi2=6/phi^4
  }
  if(x=="sqrt"){
    dphi=((1/2)*phi^(-1/2))^(-1)
    d2phi2=(-1/4)*phi^(-3/2)
  }
  ddphi<-list("dphi"=dphi,"d2phi2"=d2phi2)
}


### Standard error

stderror=function(mod,conf=0.95){

degree=3
order=2
n=mod$N
s=ncol(mod$sigma.x)
mu=mod$mu.fv
phi=mod$sigma.fv
if(is.null(mod$mu.s)==FALSE){
  p=ncol(mod$mu.x)-ncol(mod$mu.s)  
  nq=ncol(mod$mu.s)
  qj=0
  for(i in 1:nq){
    qj[i]=length(mod$mu.coefSmo[[i]]$knots)
  }
  X=as.matrix(mod$mu.x[,-which(colnames(mod$mu.x) %in% colnames(mod$mu.s))])
  bet=matrix(mod$mu.coefficients[-which(colnames(mod$mu.x) %in% colnames(mod$mu.s))], nrow=p)  
  gamms=list(NULL)
  for(i in 1:nq){
    gamms[[i]]=mod$mu.coefSmo[[i]]$coef
  }
  gamm=Reduce("rbind",gamms)
  Bs<-list(NULL)
  Ds<-list(NULL)
  for (i in 1:nq){
    ajus=pb(mod$mu.x[,which(colnames(mod$mu.x) %in% colnames(mod$mu.s)[i])],
            degree=degree,order=order,
            control=pb.control(inter=(length(mod$mu.coefSmo[[i]]$knots)-3)),
            lambda = mod$mu.lambda[i])
    Bs[[i]]=attr(ajus,"X")
    Ds[[i]]=t(attr(ajus,"D"))%*%attr(ajus,"D")*mod$mu.lambda[i]
  }
  
  B=Reduce("cbind",Bs)
  D=0.5*bdiag(Ds)
  
} else{
  p=ncol(mod$mu.x)
  bet=matrix(mod$mu.coefficients,nrow=p)
  X=mod$mu.x}

kapp=matrix(mod$sigma.coefficients,nrow=s)
E=mod$sigma.x

T1=diag(gmu(mod)$dmu,n)
T2=diag(gphi(mod)$dphi,n)

W=diag((phi^2*(trigamma(mu*phi)+trigamma((1-mu)*phi)))*gmu(mod)$dmu^2,n)
Pstar=diag((trigamma(mu*phi)*mu^2+trigamma((1-mu)*phi)*(1-mu)^2-trigamma(phi))*gphi(mod)$dphi^2,n)
Wstar=diag((phi*trigamma(mu*phi)*mu-phi*trigamma((1-mu)*phi)*
         (1-mu))*gmu(mod)$dmu*gphi(mod)$dphi,n)


Kbb= t(X)%*%W%*%X
Kkk= t(E)%*%Pstar%*%E
Kgg= t(B)%*%W%*%B+D
Kbk= t(X)%*%Wstar%*%E
Kgk= t(E)%*%Wstar%*%B
Kbg= t(X)%*%W%*%B
Kggl=t(B)%*%W%*%B
Ktt=rbind(cbind(Kbb,Kbk,Kbg),cbind(t(Kbk),Kkk,Kgk),cbind(t(Kbg),t(Kgk),Kgg))
Kttinv=ginv(as.matrix(Ktt))


coef=c(bet,kapp)
EP=sqrt(diag(Kttinv)[1:length(coef)])
VAR=diag(Kttinv)[1:length(coef)]
valorp = 0
wald =  0
for(i in 1:length(coef)){
  wald[i] = wald.test(VAR[i], coef[i], Terms = 1)$result$chi2[1]
  valorp[i] = wald.test(VAR[i], coef[i], Terms = 1)$result$chi2[3]
}


IC<-function(nconf,param, EP){
  lower<- c(param)-qnorm(1-nconf/2)*EP
  upper<- c(param)+qnorm(1-nconf/2)*EP
  obj.out <- list(IC=cbind(cbind(lower,upper)))
  return(obj.out)
}

interval=rbind(IC(1-conf, bet, EP[1:p])$IC,
               IC(1-conf, kapp, EP[(p+1):(s+p)])$IC)

coefficients = data.frame(coef, EP,  round(valorp,4), interval)
colnames(coefficients) = c("Estimate","Std.err", "Pr(>|W|)","IC-lower","IC-upper")
return(printCoefmat(as.matrix(coefficients), digits = 4))
}


### Global and local influence

influence = function(mod){

## Hessian

degree=3
order=2
n=mod$N
s=ncol(mod$sigma.x)
mu=mod$mu.fv
phi=mod$sigma.fv
if(is.null(mod$mu.s)==FALSE){
  p=ncol(mod$mu.x)-ncol(mod$mu.s)  
  nq=ncol(mod$mu.s)
  qj=0
  for(i in 1:nq){
    qj[i]=length(mod$mu.coefSmo[[i]]$knots)
  }
  X=as.matrix(mod$mu.x[,-which(colnames(mod$mu.x) %in% colnames(mod$mu.s))])
  bet=matrix(mod$mu.coefficients[-which(colnames(mod$mu.x) %in% colnames(mod$mu.s))], nrow=p)  
  gamms=list(NULL)
  for(i in 1:nq){
    gamms[[i]]=mod$mu.coefSmo[[i]]$coef
  }
  gamm=Reduce("rbind",gamms)
  Bs<-list(NULL)
  Ds<-list(NULL)
  for (i in 1:nq){
    ajus=pb(mod$mu.x[,which(colnames(mod$mu.x) %in% colnames(mod$mu.s)[i])],
            degree=degree,order=order,
            control=pb.control(inter=(length(mod$mu.coefSmo[[i]]$knots)-3)),
            lambda = mod$mu.lambda[i])
    Bs[[i]]=attr(ajus,"X")
    Ds[[i]]=t(attr(ajus,"D"))%*%attr(ajus,"D")*mod$mu.lambda[i]
  }
  
  B=Reduce("cbind",Bs)
  D=0.5*bdiag(Ds)
  
} else{
  p=ncol(mod$mu.x)
  bet=matrix(mod$mu.coefficients,nrow=p)
  X=mod$mu.x}

kapp=matrix(mod$sigma.coefficients,nrow=s)
E=mod$sigma.x

T1=diag(gmu(mod)$dmu,n)
T2=diag(gphi(mod)$dphi,n)
Phi=diag(mod$sigma.fv,n)

phi=mod$sigma.fv
mu=mod$mu.fv
Q=Qstar=S=diag(0,n)
ystar=mustar=u=0
for(i in 1:n){
  ystar[i]=log(mod$y[i]/(1-mod$y[i]))
  mustar[i]=digamma(mu[i]*phi[i])-digamma((1-mu[i])*phi[i])
  u[i]=mu[i]*(ystar[i]-mustar[i])+log(1-mod$y[i])-digamma((1-mu[i])*phi[i])+digamma(phi[i])
  Q[i,i]=(phi[i]^2*(trigamma(mu[i]*phi[i])+trigamma((1-mu[i])*phi[i]))+phi[i]*(ystar[i]-
                     mustar[i])*gmu(mod)$dmu[i]*gmu(mod)$d2mu2[i])*gmu(mod)$dmu[i]^2
  Qstar[i,i]=(phi[i]*(trigamma(mu[i]*phi[i])*mu[i]-trigamma((1-mu[i])*phi[i])*(1-mu[i]))-
                     (ystar[i]-mustar[i]))*gmu(mod)$dmu[i]*gphi(mod)$dphi[i]
  S[i,i]=(trigamma(mu[i]*phi[i])*mu[i]^2+trigamma((1-mu[i])*phi[i])*(1-mu[i])^2- trigamma(phi[i])+
                   u[i]*gphi(mod)$dphi[i]*gphi(mod)$d2phi2[i])*gphi(mod)$dphi[i]^2  
}
Ubb=-t(X)%*%Q%*%X
Ukk=-t(E)%*%S%*%E
Ugg=-t(B)%*%Q%*%B-D
Ubk=-t(X)%*%Qstar%*%E
Ugk=-t(B)%*%Qstar%*%E
Ubg=-t(X)%*%Q%*%B
Utt=rbind(cbind(Ubb,Ubg,Ubk),cbind(t(Ubg),Ugg,Ugk),cbind(t(Ubk),t(Ugk),Ukk))
Uttinv=ginv(as.matrix(-Utt))


## Leverage
M=diag(0,n)
for(i in 1:n){
  M[i,i]=1/(mod$y[i]*(1-mod$y[i]))
}
Bstar=diag(0,n)
for(i in 1:n){
  Bstar[i,i]=-(mod$y[i]-mod$mu.fv[i])/(mod$y[i]*(1-mod$y[i]))
}
if(is.null(mod$mu.s)==FALSE){
  Dmutheta=cbind(T1%*%X,T1%*%B,matrix(0,nrow=n,ncol=s))
  Uthetay=rbind(t(X)%*%T1%*%Phi%*%M,t(B)%*%T1%*%Phi%*%M,t(E)%*%T2%*%Bstar)
  lev=Dmutheta%*%Uttinv%*%Uthetay
}else{
  Dmutheta=cbind(T1%*%X,matrix(0,nrow=n,ncol=s))
  Uthetay=rbind(t(X)%*%T1%*%Phi%*%M,t(E)%*%T2%*%Bstar)
  Uttinv=solve(as.matrix(Utt))
  lev=Dmutheta%*%Uttinv%*%Uthetay
}

## Cook's Distance
cook=Uti=beti=kappi=gammi=0
for(i in 1:n){
  beti=bet+solve(-Ubb)%*%t(X[-i,])%*%T1[-i,-i]%*%Phi[-i,-i]%*%(ystar[-i]-mustar[-i])
  gammi=gamm+ginv(as.matrix(-Ugg))%*%t(B[-i,])%*%T1[-i,-i]%*%Phi[-i,-i]%*%(ystar[-i]-mustar[-i])-D%*%gamm
  kappi=kapp+solve(-Ukk)%*%t(E[-i,])%*%T2[-i,-i]%*%u[-i]
  cook[i]=t(rbind(beti,gammi,kappi)-rbind(bet,gamm,kapp))%*%Uttinv%*%(rbind(beti,gammi,kappi)-rbind(bet,gamm,kapp))
}


## Local influence - Case-weight perturbation
deltabc=t(X)%*%T1%*%Phi%*%diag((ystar-mustar),n)
deltagc=t(B)%*%T1%*%Phi%*%diag((ystar-mustar),n)
deltakc=t(E)%*%T2%*%diag(u,n)
deltacasos=rbind(deltabc,deltagc,deltakc)
Zc=t(deltacasos)%*%Uttinv%*%deltacasos
Cmaxc=abs(eigen(Zc)$vectors[,1])


## Local influence - Response perturbation
deltaby=t(X)%*%T1%*%Phi%*%M
deltagy=t(B)%*%T1%*%Phi%*%M
deltaky=t(E)%*%T2%*%Bstar
deltay=rbind(deltaby,deltagy,deltaky)
Zy=t(deltay)%*%Uttinv%*%deltay
Cmaxy=abs(eigen(Zy)$vectors[,1])


return(list(leverage=lev,
            cook=cook,
            dmaxcw=Cmaxc,
            dmaxy=Cmaxy))
}


### Plot of Leverage
# if you want to highlight a point, use the argument ref to do so

plotlev=function(mod, ref=0.4){
  lev=influence(mod)$leverage
  s1<-qplot(seq_along(diag(lev)),diag(lev),
  geom = "point",label = seq(1,length(diag(lev)),1))+ 
  xlab("Index") + ylab("Generalized Leverage") +
  geom_text_repel(aes(label=ifelse(((diag(lev))> ref),paste0(1:n),""))) +
  theme(
    panel.border = element_blank(),
    panel.grid.major = element_blank(),
    panel.grid.minor = element_blank(),
    panel.background = element_blank(),
    axis.line = element_line(colour = "grey"),
    text=element_text(size=20,family="serif")
  )
  print(s1)
}

### Plot Cook's Distance
plotcook=function(mod){
  cook=influence(mod)$cook
  s1<-qplot(seq_along(cook),cook/sum(cook),
  geom = "point",label = seq(1,length(cook),1))+ 
  xlab("Index") + ylab("Cook's Distance") +
  geom_text_repel(aes(label=ifelse(((cook/sum(cook))==max(cook/sum(cook))),
                    paste0(1:n),""))) +
  theme(
    axis.text.y=element_blank(),
    panel.border = element_blank(),
    panel.grid.major = element_blank(),
    panel.grid.minor = element_blank(),
    panel.background = element_blank(),
    axis.line = element_line(colour = "grey"),
    text=element_text(size=20,family="serif")
  )
  print(s1)
}


### Plot Case-weight perturbation
# if you want to highlight a point, use the argument ref to do so
plotcw=function(mod, ref=0.35){
  Cmaxc=influence(mod)$dmaxcw
  s1<-qplot(seq_along(Cmaxc),Cmaxc,geom = "point",
  label = seq(1,length(Cmaxc),1))+ 
  xlab("Index") + ylab(expression(d[max])) +
  geom_text_repel(aes(label=ifelse(((Cmaxc)> ref),paste0(1:n),""))) +
  theme(
    panel.border = element_blank(),
    panel.grid.major = element_blank(),
    panel.grid.minor = element_blank(),
    panel.background = element_blank(),
    axis.line = element_line(colour = "grey"),
    text=element_text(size=20,family="serif")
  )
  print(s1)
}



# Plot Response perturbation
# if you want to highlight a point, use the argument ref to do so
plotrp=function(mod, ref=0.04){
  Cmaxy=influence(mod)$dmaxy
  s1<-qplot(seq_along(Cmaxy),Cmaxy,geom = "point",
  label = seq(1,length(Cmaxy),1))+ 
  xlab("Index") + ylab(expression(d[max])) +
  geom_text_repel(aes(label=ifelse(((Cmaxy)> ref),paste0(1:n),""))) +
  theme(
    panel.border = element_blank(),
    panel.grid.major = element_blank(),
    panel.grid.minor = element_blank(),
    panel.background = element_blank(),
    axis.line = element_line(colour = "grey"),
    text=element_text(size=20,family="serif")
  )
  print(s1)
}










