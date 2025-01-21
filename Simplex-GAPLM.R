##This model was implemented in GAMLSS package
library(gamlss)
library(purrr)
library(ggplot2)
library(Matrix)
library(simplexreg)
library(matrixcalc)
library(GoFKernel)
library(pracma)
library(rootSolve)
library(ggrepel)
library(aod)
library(qqplotr)
library(MASS)
library(ggrepel)

####################################################################################
######################### Estimation process #######################################
####################################################################################

dSIM<-function (x, mu = 0.5, sigma = 1, log = FALSE) 
{
    if (any(mu <= 0)) 
        stop(paste("mu must be between 0 and 1", "\n",""))
    if (any(sigma <= 0)) 
        stop(paste("sigma must be positive", "\n",""))
    if (any(x <= 0) || any(x >= 1)) 
        stop(paste(" must be between 0 and 1", "\n",""))
    logpdf <- -((x - mu)/(mu * (1 - mu)))^2/(2 * x * (1 - x) * 
        sigma) - (log(2 * pi * sigma) + 3 * (log(x) + log(1 - 
        x)))/2
    if (!log) 
        logpdf <- exp(logpdf)
    logpdf
}

pSIM<- function(q, mu=0.5, sigma=1, lower.tail = TRUE, log.p = FALSE){
  if (any(q <= 0) || any(q >= 1)) 
        stop(paste("q must be between 0 and 1", "\n", 
            ""))
    if (any(mu <= 0) || any(mu >= 1)) 
        stop(paste("mu must be between 0 and 1", "\n", 
            ""))
    if (any(sigma <= 0)) 
        stop(paste("sigma must be positive", "\n", 
            ""))
    lp <- pmax.int(length(q), length(mu), length(sigma))
    q <- rep(q, length = lp)
    sigma <- rep(sigma, length = lp)
    mu <- rep(mu, length = lp)
    zero <- rep(0, length = lp)
    pdf <- function(x, mu, sigma) 1/sqrt(2 * pi * sigma * (x * 
        (1 - x))^3) * exp(-1/2/sigma * (x - mu)^2/(x * (1 - 
        x) * mu^2 * (1 - mu)^2))
    cdfun <- function(upper, mu, sigma) {
        int <- integrate(pdf, lower = 0, upper = upper, mu, sigma)
        int$value
    }
    Vcdf <- Vectorize(cdfun)
    cdf <- Vcdf(upper = q, mu = mu, sigma = sigma)
    if (lower.tail == TRUE) 
        cdf <- cdf
    else cdf <- 1 - cdf
    if (log.p == FALSE) 
        cdf <- cdf
    else cdf <- log(cdf)
    cdf
}

qSIM<-function(p,mu=0.5,sigma=1, lower.tail = TRUE, log.p = FALSE){
  if (any(sigma <= 0)) 
            stop(paste("sigma must be positive", "\n", 
                ""))
        if (any(mu <= 0) || any(mu >= 1)) 
            stop(paste("mu must be between 0 and 1", "\n", 
                ""))
        if (log.p == TRUE) 
            p <- exp(p)
        else p <- p
        if (lower.tail == TRUE) 
            p <- p
        else p <- 1 - p
        if (any(p < 0) | any(p > 1)) 
            stop(paste("p must be between 0 and 1", "\n", 
                ""))
        lp <- max(length(p), length(mu), length(sigma))
        p <- rep(p, length = lp)
        sigma <- rep(sigma, length = lp)
        mu <- rep(mu, length = lp)
        q <- rep(0, lp)
        h1 <- function(x, mu, sigma, p) pSIM(x, mu, sigma) - p
        uni <- function(mu, sigma, p) {
            val <- uniroot(h1, c(.Machine$double.eps, 1-.Machine$double.eps), mu = mu, sigma = sigma, 
                p = p)
            val$root
        }
        UNI <- Vectorize(uni)
        q <- UNI(mu = mu, sigma = sigma, p = p)
        q
}

rSIM<-function(n,mu=0.5,sigma=1){
  if(any(sigma<= 0)) stop(paste("sigma must be positive","\n",""))
  if(any(mu <= 0) || any(mu >=  1)) stop(paste("mu must be between 0 and 1","\n",""))
  if (any(n <= 0)) 
    stop(paste("n must be a positive integer", "\n",""))
  n <- ceiling(n)
  p <- runif(n)
  r <- qSIM(p, mu = mu, sigma = sigma)
  r
}

 
SIM<- function (mu.link = "logit", sigma.link = "log") 
{
    mstats <- checklink("mu.link", "Simplexr", substitute(mu.link), 
        c("logit", "probit", "cloglog", "cauchit", 
            "log", "own"))
    dstats <- checklink("sigma.link", "Simplexr", 
        substitute(sigma.link), c("inverse", "log", 
            "identity", "sqrt", "own"))
    structure(list(family = c("SIM", "Simplexr"), 
        parameters = list(mu = TRUE, sigma = TRUE), nopar = 2, 
        type = "Continuous", mu.link = as.character(substitute(mu.link)), 
        sigma.link = as.character(substitute(sigma.link)), mu.linkfun = mstats$linkfun, 
        sigma.linkfun = dstats$linkfun, mu.linkinv = mstats$linkinv, 
        sigma.linkinv = dstats$linkinv, mu.dr = mstats$mu.eta, 
        sigma.dr = dstats$mu.eta, dldm = function (y,mu, sigma){
          dldm <- -((mu - y) * (mu^2 + y - 2 * y * mu))/(sigma * 
                y * (y - 1) * mu^3 * (mu - 1)^3)
            dldm
         },
       d2ldm2 = function(mu,sigma){
         d <- 1/(mu^3*(1-mu)^3)
         d1<- (3*sigma)/(mu*(1-mu))
         d2ldm2 <- -((1/sigma)*(d1+d))
         d2ldm2
          
       },
       dldd = function(y,mu, sigma){
         dldd <- ((y - mu)^2)/((mu^2) * (1 - mu)^2 * y * (1 - y) * 2 * sigma^2) - (1/(2 * sigma))
          dldd
       },
       d2ldd2 = function( sigma) {
         d2ldd2 <- -1/(2*sigma^2)
           #1/(2*sigma^2)-(1/sigma^3)*((y-mu)^2/(y*(1-y)*mu^2*(1-mu)^2))
         
         d2ldd2
       },
       d2ldmdd = function(y) {
           d2ldmdd <- rep(0,length(y))
           d2ldmdd
                 }, 
       G.dev.incr = function(y, mu, sigma, ...) -2 * dSIM(y, 
            mu = mu, sigma = sigma, log = TRUE), rqres = expression(rqres(pfun = "pSIM", 
            type = "Continuous", y = y, mu = mu, sigma = sigma)), 
        mu.initial = expression(mu <- (y + mean(y))/2), sigma.initial = expression(sigma <- rep(1, 
            length(y))), mu.valid = function(mu) all(mu > 0 & 
            mu < 1), sigma.valid = function(sigma) all(sigma > 
            0), y.valid = function(y) all(y > 0 & y < 1)), class = c("gamlss.family", 
        "family"))
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
            control=pb.control(inter=length(mod$mu.coefSmo[[i]]$knots)-3))
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
p=ncol(mod$mu.x)-ncol(mod$mu.s)
nq=ncol(mod$mu.s)
mu=mod$mu.fv
phi=mod$sigma.fv
qj=0
for(i in 1:nq){
  qj[i]=length(mod$mu.coefSmo[[i]][11]$knots)
}

X=as.matrix(mod$mu.x[,-which(colnames(mod$mu.x) %in% colnames(mod$mu.s))])
bet=matrix(mod$mu.coefficients[-which(colnames(mod$mu.x) %in% colnames(mod$mu.s))], nrow=p)
kapp=matrix(mod$sigma.coefficients,nrow=s)
gamms=list(NULL)
for(i in 1:nq){
  gamms[[i]]=mod$mu.coefSmo[[i]][1]$coef
}
gamm=Reduce("rbind",gamms)

E=mod$sigma.x
Bs<-list(NULL)
Ds<-list(NULL)
for (i in 1:nq){
  ajus=pb(mod$mu.x[,which(colnames(mod$mu.x) %in% colnames(mod$mu.s)[i])],degree=degree,
          order=order,control=pb.control(inter=(length(mod$mu.coefSmo[[i]]$knots)-3)),lambda = mod$mu.lambda[i])
  Bs[[i]]=attr(ajus,"X")
  Ds[[i]]=t(attr(ajus,"D"))%*%attr(ajus,"D")*mod$mu.lambda[i]
}

B=Reduce("cbind",Bs)
D=bdiag(Ds)

T1=diag(gmu(mod)$dmu,n)
T2=diag(gphi(mod)$dphi,n)

W<- diag(as.vector((1/phi)*(((3*phi)/(mu*(1-mu)))+(1/(mu^3*(1-mu)^3)))*gmu(mod)$dmu^2),n)
P <- diag(as.vector((1/(2*phi^2))*gphi(mod)$dphi^2),n)


Kbb= t(X)%*%W%*%X
Kkk= t(E)%*%P%*%E
Kgg= t(B)%*%W%*%B+D
Kbk= matrix(0,ncol=s,nrow=p)
Kgk= matrix(0,ncol=sum(qj),nrow=s)
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
p=ncol(mod$mu.x)-ncol(mod$mu.s)
nq=ncol(mod$mu.s)
mu=mod$mu.fv
phi=mod$sigma.fv
qj=0
for(i in 1:nq){
  qj[i]=length(mod$mu.coefSmo[[i]][11]$knots)
}

X=as.matrix(mod$mu.x[,-which(colnames(mod$mu.x) %in% colnames(mod$mu.s))])
bet=matrix(mod$mu.coefficients[-which(colnames(mod$mu.x) %in% colnames(mod$mu.s))], nrow=p)
kapp=matrix(mod$sigma.coefficients,nrow=s)
gamms=list(NULL)
for(i in 1:nq){
  gamms[[i]]=mod$mu.coefSmo[[i]][1]$coef
}
gamm=Reduce("rbind",gamms)

E=mod$sigma.x
Bs<-list(NULL)
Ds<-list(NULL)
for (i in 1:nq){
  ajus=pb(mod$mu.x[,which(colnames(mod$mu.x) %in% colnames(mod$mu.s)[i])],degree=degree,
          order=order,control=pb.control(inter=(length(mod$mu.coefSmo[[1]]$knots)-3)),lambda = mod$mu.lambda[i])
  Bs[[i]]=attr(ajus,"X")
  Ds[[i]]=t(attr(ajus,"D"))%*%attr(ajus,"D")*mod$mu.lambda[i]
}

B=Reduce("cbind",Bs)
D=bdiag(Ds)

T1=diag(gmu(mod)$dmu,n)
T2=diag(gphi(mod)$dphi,n)


Phistar=diag(1/mod$sigma.fv,n)
phi=mod$sigma.fv
mu=mod$mu.fv
y=mod$y
Q=Qstar=R=U=S=diag(0,n)
d=ul=0
a=0
d =(y-mu)^2/(y*(1-y)*(mu^2)*(1-mu)^2)
a=-1/2*phi+d*(1/(2*phi^2))
U=diag((1/(mu*(1-mu)))*(d + (1/(mu^2*(1-mu)^2))),n)
ul=(2*(y-mu)*U)/(mu*(1-mu)) + (3-6*mu)/(mu^4*(1-mu)^4) + ((1-2*mu)*d)/(mu^2*(1-mu)^2)
Q=diag(as.vector((1/phi)*((diag(U)-(y-mu)*ul)+diag(U)*(y-mu)*gmu(mod)$dmu*gmu(mod)$d2mu2)*gmu(mod)$dmu^2),n)
Qstar=diag((1/phi^2)*diag(U)*(y-mu)*gmu(mod)$dmu*gphi(mod)$dphi,n)
S=diag((1/(2*phi^2)-1/phi^3*d+a*gphi(mod)$dphi*gphi(mod)$d2phi2)*gphi(mod)$dphi^2,n)

Ubb=-t(X)%*%Q%*%X
Ukk=-t(E)%*%S%*%E
Ugg=-t(B)%*%Q%*%B-D
Ubk= -t(X)%*%Qstar%*%E
Ugk=-t(B)%*%Qstar%*%E
Ubg=-t(X)%*%Q%*%B
Uggl=-t(B)%*%Q%*%B
Utt=rbind(cbind(Ubb,Ubg,Ubk),cbind(t(Ubg),Ugg,Ugk),cbind(t(Ubk),t(Ugk),Ukk))
Uttinv=ginv(as.matrix(-Utt))

## Leverage

M=Bstar=diag(0,n)
d=(y-mu)^2/(y*(1-y)*(mu^2)*(1-mu)^2)
M=diag((1/(phi*mu^3*(1-mu)^3))*((3*(y-mu)^2/(y*(1-y)))-((1-2*y)*(y-mu)^3/(y^2*(1-y)^2))+1),n)
Bstar=diag((1/(2*phi^2*y*(1-y)))*((2*(y-mu)/(mu^2*(1-mu)^2))-d*(1-2*y)),n)
Dmutheta=cbind(T1%*%X,T1%*%B,matrix(0,nrow=n,ncol=s))
Uthetay=cbind(t(t(X)%*%T1%*%Phistar%*%M),t(t(B)%*%T1%*%Phistar%*%M),t(t(E)%*%T2%*%Bstar))
lev=Dmutheta%*%Uttinv%*%t(Uthetay)

## Cook's Distance
cook=Uti=beti=kappi=gammi=0
for(i in 1:n){
  beti=bet+solve(-Ubb)%*%t(X[-i,])%*%T1[-i,-i]%*%U[-i,-i]%*%Phistar[-i,-i]%*%(y[-i]-mu[-i])
  gammi=gamm+ginv(as.matrix(-Ugg))%*%t(B[-i,])%*%T1[-i,-i]%*%U[-i,-i]%*%Phistar[-i,-i]%*%(y[-i]-mu[-i])-D%*%gamm
  kappi=kapp+solve(-Ukk)%*%t(E[-i,])%*%T2[-i,-i]%*%a[-i]
  cook[i]=t(rbind(beti,gammi,kappi)-rbind(bet,gamm,kapp))%*%Uttinv%*%(rbind(beti,gammi,kappi)-rbind(bet,gamm,kapp))
}

## Local influence - Case-weight perturbation
deltabc=t(X)%*%T1%*%U%*%Phistar%*%diag((y-mu),n)
deltagc=t(B)%*%T1%*%U%*%Phistar%*%diag((y-mu),n)
deltakc=t(E)%*%T2%*%diag(a,n)
deltacasos=rbind(deltabc,deltagc,deltakc)
Zc=t(deltacasos)%*%Uttinv%*%deltacasos
Cmaxc=Re(eigen(Zc)$vectors[,1])

## Local influence - Response perturbation
deltaby=t(X)%*%T1%*%Phistar%*%M
deltagy=t(B)%*%T1%*%Phistar%*%M
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







