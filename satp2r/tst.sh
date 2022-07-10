#!/bin/bash

#---- Selected instances ----------------

arr_inst=(
allSatTst7.txt \
ac_1024_1.txt \
ak_1022.txt \
AK_262142.txt \
Dy1CtVS_VSA3_dynamic1.txt \
Genrmf_Long_4096_1.txt \
Netgen_n1000_d0.01_c1000_1.txt \
Transit_Grid_18.txt \
Transit_Grid_1way_n2502_c100_1.txt \
Transit_Grid_2way_n38_c10000_5.txt \
Wash_Cher_n128_m128_c128_1.txt \
Wash_DExpoLine_r32_co32_d16_1.txt \
Wash_DinicBad_n1024.txt \
Wash_ExpoLine_r32_co32_d16_1.txt \
Wash_ExpoLine_r3_co729_d27_1.txt \
Wash_GldBad_n3003_1.txt \
Wash_Line_r32_co32_d16_1.txt \
Wash_Mesh_r10_co12_c100_1.txt \
)

#-------------- Algorithm --------------

arr_alg=( p2r sa_p2r ss_p2r sl_p2r sag_p2r ssg_p2r slg_p2r )

#--------------Directories------------------------
main_dir=/data/gpfs/projects/punim0836/C/maxflow_implementations/Static/Source/OCs/satp2r


#-------------------------------------------------

cd $main_dir


for alg in ${arr_alg[*]}
do
	echo "$alg"
	> test_results_$alg

	for inst in ${arr_inst[*]}
	do
		echo "**********************************" >> $main_dir/test_results_$alg
		echo "$inst" >> $main_dir/test_results_$alg
		$main_dir/$alg < $main_dir/$inst >> $main_dir/test_results_$alg
		echo " " >> $main_dir/test_results_$alg
		echo " " >> $main_dir/test_results_$alg
	done
done
