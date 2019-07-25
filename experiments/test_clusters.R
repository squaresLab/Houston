library("optparse")
library("yaml")

option_list = list(
  make_option("--data_dir", type="character", default=NULL, 
              help="path to the data directory."),
  make_option(c("-c", "--command"), type="character", default=NULL, 
              help="desired command."),
  make_option("--rdata", type="character", default=NULL,
              help="RData file."),
  make_option("--output_dir", type="character", default="", 
              help="path to the output directory.")
); 

opt_parser = OptionParser(option_list=option_list);
opt = parse_args(opt_parser);

if(is.null(opt$data_dir) || is.null(opt$command) || is.null(opt$rdata)) {
  print_help(opt_parser)
  stop("Required arguments missing!")
}

data_dir <- opt$data_dir
output_dir <- opt$output_dir
command <- opt$command

load(opt$rdata)

lowest_dist <- function(mvc, data) {
    best_dist = 1000000000000
    for (c in mvc@centroids) {
        d = dtw::dtw(data, c)
        if (d$distance < best_dist){
            best_dist = d$distance
        }
    }
    return(best_dist)
}

mission_and_index <- function(filename) {

    name_parts = unlist(strsplit(filename, split="_"))
    mission = name_parts[length(name_parts) -1]
    index = unlist(strsplit(name_parts[length(name_parts)], split="\\."))[1]
    return(paste(mission, index, sep="_"))
}

allfiles <- list.files(path=data_dir, pattern=paste("factory.", command, ".+.csv", sep=""), full.names=TRUE, recursive=FALSE)

dists <- list()
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
  name = mission_and_index(f)
  dists[name] <- lowest_dist(final_mvc, as.matrix(m))
}

if (length(myData) == 0) {
    cat("The data is empty for command", command)
    quit()
}

print("done")
print(command)
write(as.yaml(dists), file=paste(output_dir, command, ".yml", sep=""))
