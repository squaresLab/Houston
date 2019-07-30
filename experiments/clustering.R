library("dtwclust")
library("optparse")

option_list = list(
  make_option("--data_dir", type="character", default=NULL, 
              help="path to the data directory."),
  make_option(c("-c", "--command"), type="character", default=NULL, 
              help="desired command."),
  make_option("--output_dir", type="character", default="", 
              help="path to the output directory."),
  make_option("--list_of_vars", type="character", default=NULL,
              help="comma separated list of variables to consider for clustering"),
  make_option(c("-n", "--dp_num"), type="integer", default=-1,
              help="number of datapoints per trace."),
  make_option(c("-k", "--clusters"), type="integer", default=3, 
              help="number of clusters (k)."),
  make_option("--fuzzy", action="store_true", default=FALSE, 
              help="run the clustering in fuzzy mode."),
  make_option("--select_best_k", action="store_true", default=FALSE,
              help="select best k out of k, k-1 and k+1"),
  make_option("--seed", type="integer", default=0,
              help="the random seed")
); 

opt_parser = OptionParser(option_list=option_list);
opt = parse_args(opt_parser);

if(is.null(opt$data_dir) || is.null(opt$command)) {
  print_help(opt_parser)
  stop("Required arguments missing!")
}

dist <- "dtw"
varlist = NULL
if(!is.null(opt$list_of_vars)){
  varlist = unlist(strsplit(opt$list_of_vars, split=","))
}

allfiles <- list.files(path=opt$data_dir, pattern=paste("factory.", opt$command, ".+.csv", sep=""), full.names=TRUE, recursive=FALSE)

myData <- list()
files <- vector()
i <- 1
n <- opt$dp_num
for (f in allfiles) {
  m <- read.csv(f, header=TRUE)
#  m <- as.matrix(m)
  if (is.null(varlist)){
    varlist = colnames(m)
  }
  m <- m[,varlist]
  if (n != -1) {
    l <- floor(length(m[, 1]) / n)
    if (l == 0) {
        next
    }
    m <- m[seq(0, n-1) * l + 1 , ]
  }
  myData[[i]] <- as.matrix(m)
  files[i] <- f
  i <- i+1
}

write(files, file=paste(opt$output_dir, opt$command, "_files.txt", sep=""))

if (length(myData) == 0) {
    cat("The data is empty for command", opt$command)
    quit()
}

#myData2 <- zscore(myData)
#m <- read.csv(files[1], header=TRUE)

total_dist <- function(mvc) {
    s <- sum(mvc@clusinfo$av_dist * mvc@clusinfo$size)
    return(s + (s/6) * length(mvc@clusinfo$size))
}
select_best_mvc <- function(mvc) {
    if (length(mvc) == 1) {
        return(mvc)
    }
    best_mvc = NULL
    best_dist = 1000000000000
    for (m in mvc) {
        t = total_dist(m)
        if (t < best_dist){
            best_mvc = m
            best_dist = t
        }
    }
    print("Best k is")
    print(length(best_mvc@clusinfo$size))
    return(best_mvc)
}


if(opt$select_best_k) {
    k <- c(opt$clusters - 1, opt$clusters, opt$clusters + 1)
} else {
    k <- c(opt$clusters)
}

if (!opt$fuzzy) {
    mvc <- tsclust(myData, k = k, distance = dist, seed = opt$seed)
} else {
    mvc <- tsclust(myData, k = k, type = "fuzzy", seed = opt$seed)
}

print(mvc)
final_mvc <- select_best_mvc(mvc)

pdf(paste(opt$output_dir, opt$command, ".pdf", sep=""))
plot(final_mvc)
dev.off()
write(paste("Int64", toString(final_mvc@cluster), sep = "\n"), file=paste(opt$output_dir, opt$command, "_labels.txt", sep=""))
save.image(file=paste(opt$output_dir, opt$command, ".RData", sep=""))

print(final_mvc@clusinfo)

