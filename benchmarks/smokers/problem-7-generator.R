# Problem 7: Friends and Smokers
# Tom Dietterich June 2014
#
# number of nodes in the graph
num.people <- 20
# num.pairs <- (num.people * (num.people  - 1))/2
# the edges. Filled symmetrically; 0 on diagonal
edges <- matrix(0, nrow = num.people, ncol = num.people)
# 
edge.density <- 1/10
for (i in 1:(num.people - 1)) {
  for (j in (i+1):num.people) {
    friends <- rbinom(1, 1, edge.density)
    edges[i,j] <- friends
    edges[j,i] <- friends
  }
}

# write out the graph
# note: I hand-edited the row and column names to make them readable
write.csv(edges, "problem-7-friends.csv")

######################################################################
##
## checking the generated graph
#
#  how many connected components?
library(igraph)
g <- graph.adjacency(edges, mode = "undirected")
no.clusters(g)
#

######################################################################
##
## rudimentary Gibbs sampler

#
# Now we need to assign smoking status
# First randomly assign to each node based on prior
smokes <- rbinom(num.people, 1, 0.2)

# MRF potentials
node.potential <- function(i) {
  if (smokes[i]==0) { return(-0.22314) } else { return (-1.60943) }
}
edge.potential <- function(i,j) {
  if (smokes[i] == smokes[j]) { return(0.549306) } else { return(-0.549306) }
}

# probability that node i is a smoker conditioned on the smoking
# status of its neighbors 
# TGD: took me a while to figure out that I needed outer assigns
psmokes <- function (i) {
  was <- smokes[i]
  smokes[i] <<- 0
  pot0 <- node.potential(i)
  for (j in 1:num.people) {
    if (edges[i,j] == 1) {
       pot0 <- pot0 + edge.potential(i,j)
    }
  }
  smokes[i] <<- 1
  pot1 <- node.potential(i)
  for (j in 1:num.people) {
    if (edges[i,j] == 1) {
       pot1 <- pot1 + edge.potential(i,j)
    }
  }
  smokes[i] <<- was
  return (exp(pot1) / (exp(pot0) + exp(pot1)))
}


# The Gibbs sampler
smokes <- rbinom(num.people, 1, 0.2)
niter <- 10000
record <- matrix(0, nrow=niter, ncol=num.people)
for (iter in 1:niter) {
  record[iter,] <- smokes
  for (i in 1:num.people) {
    smokes[i] <- rbinom(1, 1, psmokes(i))
  }
}

marginals <- rep(0, num.people)
neighbors <- rep(0, num.people)
for (i in 1:num.people) {
  marginals[i] <- mean(record[,i])
  neighbors[i] <- sum(edges[i,])
}
plot(neighbors, marginals)

###################################################
## Problem 7 query
##

# bind the smoking status
bound <- rep(FALSE, num.people)
smokes <- rep(0, num.people)

# 9 is half of the 14-9 pair
bound[9]  = TRUE
smokes[9] = 1
# 8-15-18-11-1 is a chain
bound[8]  = TRUE
smokes[8] = 1

bound[15]  = TRUE
smokes[15] = 1

bound[1]   = TRUE
smokes[1]  = 1
# 2 neighbors of 3 will be set to 0
bound[4]   = TRUE
smokes[4]  = 0

bound[6]   = TRUE
smokes[6]  = 0

# modified Gibbs sampler only flips the non-bound variables
record <- matrix(0, nrow=niter, ncol=num.people)
for (iter in 1:niter) {
  record[iter,] <- smokes
  for (i in 1:num.people) {
    if (!bound[i]) {
      smokes[i] <- rbinom(1, 1, psmokes(i))
    }
  }
}

# visualize the answer
marginals <- rep(0, num.people)
neighbors <- rep(0, num.people)
for (i in 1:num.people) {
  marginals[i] <- mean(record[,i])
  neighbors[i] <- sum(edges[i,])
}
plot(neighbors, marginals)

# compute performance profile in terms of number of iterations
# TODO: include CPU time in an array parallel to record
# possibly include a burnin period to ignore the transient period
totals <- rep(0,num.people)
profile <- matrix(0, nrow=niter, ncol=num.people)
for (iter in 1:niter) {
  totals <- totals + record[iter,]
  profile[iter,] <- totals / iter
}
