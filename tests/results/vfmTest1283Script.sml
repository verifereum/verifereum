Theory vfmTest1283[no_sig_docs]
Ancestors vfmTestDefs1283
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1283_0.nsv", "result1283_1.nsv", "result1283_2.nsv", "result1283_3.nsv", "result1283_4.nsv", "result1283_5.nsv", "result1283_6.nsv", "result1283_7.nsv", "result1283_8.nsv", "result1283_9.nsv", "result1283_10.nsv", "result1283_11.nsv", "result1283_12.nsv", "result1283_13.nsv", "result1283_14.nsv", "result1283_15.nsv", "result1283_16.nsv", "result1283_17.nsv"];
val thyn = "vfmTestDefs1283";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
