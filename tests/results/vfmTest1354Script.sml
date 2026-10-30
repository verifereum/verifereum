Theory vfmTest1354[no_sig_docs]
Ancestors vfmTestDefs1354
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1354_0.nsv", "result1354_1.nsv", "result1354_2.nsv", "result1354_3.nsv", "result1354_4.nsv", "result1354_5.nsv", "result1354_6.nsv", "result1354_7.nsv", "result1354_8.nsv", "result1354_9.nsv", "result1354_10.nsv", "result1354_11.nsv", "result1354_12.nsv", "result1354_13.nsv", "result1354_14.nsv", "result1354_15.nsv", "result1354_16.nsv", "result1354_17.nsv", "result1354_18.nsv", "result1354_19.nsv", "result1354_20.nsv", "result1354_21.nsv", "result1354_22.nsv", "result1354_23.nsv"];
val thyn = "vfmTestDefs1354";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
