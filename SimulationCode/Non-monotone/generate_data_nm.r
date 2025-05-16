###########################################################################
#Program name           : generate_data_nm.R
#Programmer / Location  : Yoshinori Takeuchi 
#                   (Department of Data Science, Yokohama City University)
#Date                   : 06 January 2025
#Comment                : This program is a modified version of "generate_data.R" provided by Seaman et al., 2020.
###########################################################################

#----------------------
# Load required package
#----------------------
library(MASS)
library(dplyr)

#----------------------
# Parameter values
# mu, alpha, beta, gamma, delta, phi and Lvar are parameters of the data-generating mechanism for A_k, L_k and the failure times.
# In particular, delta describes the effects of the treatments on the hazard of failure, and phi describes the interactions between A and the history of La in these effects of treatment.
#----------------------

# mu, alpha, beta are parameters of the conditional distribution of L_k.
# gamma, delta and phi are parameters of the conditional hazard model
mu <- matrix(0, (K+1)*2, K+1)
alpha <- matrix(0, (K+1)*2, (K+1)*2)
beta <- matrix(0, (K+1)*2, K+1)
gamma <- matrix(0, K+1, (K+1)*2)
delta <- matrix(0, K+1, K+1)
phi <- matrix(0, K+1, K+1)
Lvar <- matrix(c(0.5, 0.2, 0.2, 0.5), 2, 2)
  
for (j in 1:K)
  alpha[j*2+(1:2), (j-1)*2+(1:2)] <- c(0.2, 0.2, 0.1, 0.1)
for (j in 1:K)
  beta[j*2+(1:2), j] <- c(0.1, 0.05)
for (j in 1:(K+1))
  gamma[j, 2*(j-1)+(1:2)] <- 0.03

# delta[k+1,] describes the effects of A_0, ..., A_K on the hazard rate between the kth and (k+1)th exposure times.
if (EFFECT=="harmful") {
  delta[1,1] <- 0.04
  delta[2, 1:2] <- c(0.01, 0.04)
  if (K>1)
    delta[3, 1:3] <- c(0.004, 0.01, 0.04)
  if (K>2)
    delta[4, 1:4] <- c(0.002, 0.004, 0.01, 0.04)
}

if (EFFECT=="null") {
  delta[1,1] <- 0
  delta[2, 1:2] <- c(0, 0)
  if (K>1)
    delta[3, 1:3] <- c(0, 0, 0)
  if (K>2)
    delta[4, 1:4] <- c(0, 0, 0, 0)
}

if (EFFECT=="beneficial") {
  delta[1,1] <- -0.04
  delta[2, 1:2] <- c(-0.01, -0.04)
  if (K>1)
    delta[3, 1:3] <- c(-0.004, -0.01, -0.04)
  if (K>2)
    delta[4, 1:4] <- c(-0.002, -0.004, -0.01, -0.04)
}

# Allowing an interaction between treatment and the confounders La.
if (EFFECT.MODIFICATION) {
  phi[1,1] <- 0.004
  phi[2, 1:2] <- c(0.002, 0.004)
  if (K>1)
    phi[3, 1:3] <- c(0, 0.002, 0.004)
  if (K>2)
    phi[4, 1:4] <- c(0, 0, 0.002, 0.004)
}

# Now calculate the true values of psi.
# psiA.true[k+1, l+1,] is the true effect of A_k on the hazard between times l and l+1.
psiA.true <- array(0, c(K+1, K+1, EFFECT.MODIFICATION+1))

h <- beta
if (K>1)
  for (j in 2:K)
    for (k in 0:(j-2))
      for (l in (k+1):(j-1))
        h[j*2+(1:2), k*2+1:2] <- h[j*2+(1:2), k*2+1:2] + alpha[j*2+(1:2), l*2+(1:2)] %*% h[l*2+(1:2), k*2+1:2]

psiA.true[,, 1] <- t(delta)
if (K>1)
  for (k in 0:(K-1))
    for (l in 1:(K-k))
      for (j in (k+1):(k+l))
        psiA.true[k+1, k+l+1, 1] <- psiA.true[k+1, k+l+1, 1] + gamma[k+l+1, (j*2)+1:2] %*% h[(j*2)+1:2, k+1]

if (EFFECT.MODIFICATION)
  psiA.true[,, 2] <- t(phi)

print("True values of psiA are")
print(psiA.true)

#----------------------
# Generate a dataset
#----------------------

set.seed(712*s)

#Missing parameters
delta00 <- Mbasep
deltaA <- log(1.5)
deltaL <- 0.8
deltaV <- log(0.8)
deltaF <- log(5.0)
deltaT <- log(1.2)
deltaM <- log(1.2)
gammaL <- -0.2

# Matrices where the data will be stored
# A is the treatment.
# L is a vector of confounders: here we assume two confounders at each time-point (La and Lb).  Hence, there are 2*(K+1) confounders in total.
# tau are the individual exposure times, apart from the last (tau[,K+2]), which is the (random) administrative censoring time. The first exposure time is zero.
# rate is the hazard rate.
A <- matrix(0, N, K+1)
pA <- matrix(0, N, K+1)
colnames(A) <- paste("A", 0:K, sep="")
L <- matrix(0, N, 2*(K+1))
pL2 <- matrix(0, N, K+1)
Mprob <- matrix(0, N, K+1)
MLb <- matrix(0, N, K+1)
colnames(L) <- paste(c("La", "Lb"), rep(0:K, each=2), sep="")
tau <- matrix(0, N, K+2)
rate <- matrix(0, N, K+1)

U <- matrix(0, N, 1)
U[,1] <- runif(N,0,1)
V <- matrix(0, N, 1)
V[,1] <- rbinom(N,1,0.5)

baserate <- rep(0.34, K+1)

# Generate timepoints
for (j in 2:(K+1))
  tau[,j] <- tau[,j-1] + 1

# There is administrative censoring at time admin.cens.time
admin.cens.time <- K+1
tau[, K+2] <- admin.cens.time
tau[tau[, K+2] <= tau[,K+1], K+2] <- tau[tau[,K+2] <= tau[,K+1], K+1] + 0.001
# That last line is just to make sure that tau[,K+2] > tau[,K+1] (in practice
# such an individual will be censored or fail at or before time admin.cens.time
# anyway).

# Generate A and L
if (MISSTYPE=="gaussian"){
L[, 1:2] <- mvrnorm(N, mu[1:2, 1], Lvar)+0.5*U[,1]-0.2*V[,1]
} 
if (MISSTYPE=="binomial"){
L[, 1:2] <- mvrnorm(N, mu[1:2, 1], Lvar)+0.5*U[,1]-0.2*V[,1]
pL2[, 1] <- (exp(-0.5+log(1.2)*L[,1]+0.5*U[,1]-0.2*V[,1])/(1+exp(-0.5+log(1.2)*L[,1]+0.5*U[,1]-0.2*V[,1])))
L[,2] <- rbinom(N,1,pL2[, 1])
}
if (EXPOSETYPE=="gaussian"){
A[,1] <- rnorm(N, mean=3+L[,1]/5+L[,2]/10+V[,1]/5, sd=0.9)
}
if (EXPOSETYPE=="binomial"){
  pA[, 1] <- (exp(-0.5+log(1.5)*L[,1]+0.8*L[,2]-0.2*V[,1])/(1+exp(-0.5+log(1.5)*L[,1]+0.8*L[,2]-0.2*V[,1])))
  A[, 1] <- rbinom(N,1,pA[, 1])
}
rate[, 1] <- baserate[1] + U[,1]*gamma[1, (1:2)] + 0.5*V[,1]*gamma[1, (1:2)] + as.matrix(A[, 1:1]) %*% delta[1, 1:1] + as.matrix(A[, 1:1] * L[, (0:0)*2+1]) %*% phi[1, 1:1]
rate[,1][rate[,1]<0] <- 0.0001

# There is administrative censoring at time admin.cens.time and random
# censoring by an exponential variable
censrate <- 0.2
cens <- pmin(rexp(N, censrate), admin.cens.time)

# Generate failure times
tims <- matrix(0, N, K+1)
fails <- matrix(0, N, K+1)
tims[,1] <- rexp(N, rate[, 1]) + tau[,1]
fails[,1] <- (tims[,1] <= cens)&(tims[,1] <= tau[,2])
tims[,1] <- ifelse(tims[,1]>cens,cens,tims[,1])
tims[,1] <- ifelse(tims[,1]>tau[,2],(tau[,2]-tau[,1]),(tims[,1]-tau[,1]))

# Missing of Lb
Mprob[, 1] <- (exp(delta00+deltaA*A[,1]+deltaV*V[,1]+deltaL*L[,1]+gammaL*L[,2]+deltaF*fails[,1]+deltaT*tims[,1])/(1+exp(delta00+deltaA*A[,1]+deltaV*V[,1]+deltaL*L[,1]+gammaL*L[,2]+deltaF*fails[,1]+deltaT*tims[,1])))
MLb[, 1] <- rbinom(N,1,Mprob[, 1])
L[, 2][MLb[,1]==1]<-0

for (k in 1:K) {
  if (MISSTYPE=="gaussian"){
  L[, k*2+(1:2)] <- mvrnorm(N, mu[k*2+(1:2), k+1], Lvar) + L[, (k-1)*2+(1:2)] %*% alpha[k*2+(1:2), (k-1)*2+(1:2)] + A[, 1:k] %*% t(beta[k*2+(1:2), 1:k]) - 0.5*MLb[, 1:k] %*% t(beta[k*2+(1:2), 1:k]) + 0.5*U[,1] - 0.2*V[,1]
  }
  if (MISSTYPE=="binomial"){
  L[, k*2+(1:2)] <- mvrnorm(N, mu[k*2+(1:2), k+1], Lvar) + L[, (k-1)*2+(1:2)] %*% alpha[k*2+(1:2), (k-1)*2+(1:2)] + A[, 1:k] %*% t(beta[k*2+(1:2), 1:k]) - 0.5*MLb[, 1:k] %*% t(beta[k*2+(1:2), 1:k]) + 0.5*U[,1] - 0.2*V[,1]
  pL2[, k+1] <- (exp(-0.5+log(1.5)*A[,k]+log(1.2)*L[,k*2+1]+log(0.8)*L[,(k-1)*2+2]+log(0.5)*MLb[,k]+0.5*U[,1]-0.2*V[,1])/(1+exp(-0.5+log(1.5)*A[,k]+log(1.2)*L[,k*2+1]+log(0.8)*L[,(k-1)*2+2]+log(0.5)*MLb[,k]+0.5*U[,1]-0.2*V[,1])))
  L[, k*2+2] <- rbinom(N,1,pL2[, k+1])
  }
  if (EXPOSETYPE=="gaussian"){
  A[, k+1] <- rnorm(N, mean=2+0.5*A[,k]+L[,k*2+1]/10 + L[,k*2+2]/20-0.2*MLb[,k]+V[,1]/5, sd=0.7)
  }
  if (EXPOSETYPE=="binomial"){
  pA[, k+1] <- (exp(-0.5+log(3.0)*A[,k]+log(1.5)*L[,k*2+1]+0.8*L[,k*2+2]+0.1*MLb[,k]-0.2*V[,1])/(1+exp(-0.5+log(3.0)*A[,k]+log(1.5)*L[,k*2+1]+0.8*L[,k*2+2]+0.1*MLb[,k]-0.2*V[,1])))
  A[, k+1] <- rbinom(N,1,pA[, k+1])
  }
  
  rate[, k+1] <- baserate[k+1] + U[,1]*gamma[k+1, k*2+(1:2)] + 0.5*V[,1]*gamma[k+1, k*2+(1:2)] + as.matrix(A[, 1:(k+1)]) %*% delta[k+1, 1:(k+1)] + as.matrix(A[, 1:(k+1)] * L[, (0:k)*2+1]) %*% phi[k+1, 1:(k+1)]
   rate[rate<0] <- 0.0001
  
  tims[,k+1] <- rexp(N, rate[, k+1]) + tau[,k+1]
  fails[,k+1] <- (tims[,k+1] <= cens)&(tims[,k+1] <= tau[,k+2])
  tims[,k+1] <- ifelse(tims[,k+1]>cens,cens,tims[,k+1])
  tims[,k+1] <- ifelse(tims[,k+1]>tau[,k+2],(tau[,k+2]-tau[,k+1]),(tims[,k+1]-tau[,k+1]))
  tims[,k+1] <- ifelse(tims[,k]<(tau[,k+1]-tau[,k]),0,tims[,k+1])
  fails[,k+1] <- ifelse(tims[,k+1]==0,0,fails[,k+1])
  Mprob[, k+1] <- (exp(delta00+deltaA*A[,k+1]+deltaV*V[,1]+deltaL*L[,(2*k)+1]+gammaL*L[,(2*k)+2]+deltaF*fails[,k+1]+deltaT*tims[,k+1]-deltaM*MLb[,k])/(1+exp(delta00+deltaA*A[,k+1]+deltaV*V[,1]+deltaL*L[,(2*k)+1]+gammaL*L[,(2*k)+2]+deltaF*fails[,k+1]+deltaT*tims[,k+1]-deltaM*MLb[,k])))
  MLb[, k+1] <- rbinom(N,1,Mprob[, k+1])
  L[, k*2+2][MLb[,k+1]==1]<-0
}

for (k in 0:K) {
  L[, k*2+2][MLb[,k+1]==1]<-NA
}

fail <- rowSums(fails)
tim <- rowSums(tims)

nfail <- rep(0, K+1)
ncens <- rep(0, K+1)

# Count the numbers of failures and censorings in each interval between exposures
for (k in 0:K) {
  nfail[k+1] <- sum(tim >= tau[, k+1] & tim < tau[, k+2] & fail==1)
  ncens[k+1] <- sum(tim >= tau[, k+1] & tim < tau[, k+2] & fail==0)
}
print("Numbers of failures in each interval are")
print(nfail)
print("Numbers of censorings in each interval are")
print(ncens)
