for f in ./cbmc_*.c
do
 echo "Processing $f"
 base_name=$(basename -- "$f" .c)
 #echo $base_cnfname
 cbmc $f --dimacs --outfile ${base_name}.cnf &> log_cbmc_${base_name} &
done

#cnfname=$1
#base_cnfname=$(basename -- "$cnfname" .c)
##echo $base_cnfname
#cbmc $cnfname --dimacs --outfile ${base_cnfname}.cnf &> log_cbmc_${base_cnfname} &
