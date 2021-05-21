# install thesis with install.package("<package-name") in the R interpreter
library(ggplot2)
library(dplyr)
library(tidyr)
library(broom)
library(scales)
library(purrr)
library(ggrepel)

data_file0 <- "enronEmail1-5.csv"
data_file1 <- "employee1-5.csv"

## these have extra tuples
data_file2 <- "employee-NBF(f).csv"
data_file3 <- "employee-UBF(f).csv"
data_file4 <- "enronEmail-NBF(f).csv"
data_file5 <- "employee-NBF-comp-filter.csv"
data_file6 <- "employee-NBF(i)-comp-filter.csv"
data_file7 <- "enronEmail-NBF-comp-filter.csv"
data_file8 <- "enronEmail-NBF(i)-comp-filter.csv"

files_bar     <- c("enronEmail1-5.csv", "employee1-5.csv", "employee-NBF(f).csv", "employee-UBF(f).csv", "enronEmail-NBF(f).csv", "employee-NBF-comp-filter.csv", "employee-NBF(i)-comp-filter.csv", "enronEmail-NBF-comp-filter.csv", "enronEmail-NBF(i)-comp-filter.csv")

files_scatter <- c( "employee-NBF(f).csv", "employee-UBF(f).csv", "enronEmail-NBF(f).csv", "employee-NBF-comp-filter.csv", "employee-NBF(i)-comp-filter.csv", "enronEmail-NBF-comp-filter.csv", "enronEmail-NBF(i)-comp-filter.csv")


options(ggrepel.max.overlaps = Inf)

plotBreaks <- function(x) {seq(0,max(x),5)}

mk_data_frame <- function(f) {
  read.csv(file=f) %>% mutate(Query = as.factor(Query),
                              Approach = as.factor(Approach)) %>%
    na.exclude()
}


mk_bar_plt <- function(f) {

  df <- mk_data_frame(f)

  pl <- ggplot(df, aes(x=Approach, y=Time)) +
    geom_bar(stat="identity", aes(fill=Approach, color=Approach)) +
    facet_grid(. ~ Query, scales = "free_x") +
    theme_classic() +
    # theme(axis.text.x = element_text(angle=90,vjust=0.5,hjust=1)) +
    theme(
        axis.text.x=element_blank(),
        axis.ticks.x=element_blank()) +
    xlab("Approaches") +
    scale_y_continuous(breaks=plotBreaks) +
    ylab("Time [Sec.] ")

  pl
}


mk_scatter_plt <- function(f) {
  df <- read.csv(file=f) %>% mutate(Query = as.factor(Query),
                                    Approach = as.factor(Approach))

  pl <- ggplot(df, aes(x=Tuples, y=Time, colour=Approach)) +
    geom_point(aes(color=Approach,shape=Approach)
      ,alpha=0.7,size=4) +
    # geom_text(aes(label=Query), show.legend=FALSE)+
    # geom_text(aes(label=Query),hjust=0, vjust=0)+
    geom_label_repel(aes(label = Query))+
                  # segment.color = 'grey50') +
    # geom_line(aes(color=Approach)) +
    scale_x_continuous(labels=comma) +
    # scale_x_log10(labels=comma) +
    theme_classic() +
    scale_shape_manual(values = c(16,17)) +
    ylab("Time [Sec.] ") +
    xlab("Number of Tuples")

    # geom_jitter()
# wt, mpg, label = rownames(mtcars), colour = factor(cyl))) +
#   geom_point()
  pl
}

## the map is equivalent to: fmap mk_bar_plot file_bar
## %>% is just forward composition
plots <- files_bar %>% map(mk_bar_plt)

plt0 <- mk_bar_plt(data_file0)
plt1 <- mk_bar_plt(data_file1)
plt2 <- mk_bar_plt(data_file2)
plt3 <- mk_bar_plt(data_file3)
plt4 <- mk_bar_plt(data_file4)
plt5 <- mk_bar_plt(data_file5)
plt6 <- mk_bar_plt(data_file6)
plt7 <- mk_bar_plt(data_file7)
plt8 <- mk_bar_plt(data_file8)

pltsct2 <- mk_scatter_plt(data_file2)
pltsct3 <- mk_scatter_plt(data_file3)
pltsct4 <- mk_scatter_plt(data_file4)
pltsct5 <- mk_scatter_plt(data_file5)
pltsct6 <- mk_scatter_plt(data_file6)
pltsct7 <- mk_scatter_plt(data_file7)
pltsct8 <- mk_scatter_plt(data_file8)


## ggsave("employee1_5.png", plot = empy1_5_plt, height = 4, width = 7, device = "png")
## ggsave("../plots/RQ1_Fin.png", plot = rq1Fin, height = 4, width = 7, device = "png")
