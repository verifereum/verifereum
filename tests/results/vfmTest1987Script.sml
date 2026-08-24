Theory vfmTest1987[no_sig_docs]
Ancestors vfmTestDefs1987
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1987_0.nsv", "result1987_1.nsv", "result1987_2.nsv", "result1987_3.nsv", "result1987_4.nsv", "result1987_5.nsv", "result1987_6.nsv", "result1987_7.nsv", "result1987_8.nsv", "result1987_9.nsv", "result1987_10.nsv", "result1987_11.nsv", "result1987_12.nsv", "result1987_13.nsv", "result1987_14.nsv", "result1987_15.nsv", "result1987_16.nsv", "result1987_17.nsv", "result1987_18.nsv", "result1987_19.nsv"];
val thyn = "vfmTestDefs1987";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
