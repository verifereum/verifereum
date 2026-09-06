Theory vfmTest1688[no_sig_docs]
Ancestors vfmTestDefs1688
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1688_0.nsv", "result1688_1.nsv", "result1688_2.nsv", "result1688_3.nsv", "result1688_4.nsv", "result1688_5.nsv", "result1688_6.nsv", "result1688_7.nsv", "result1688_8.nsv", "result1688_9.nsv", "result1688_10.nsv", "result1688_11.nsv", "result1688_12.nsv", "result1688_13.nsv", "result1688_14.nsv", "result1688_15.nsv", "result1688_16.nsv", "result1688_17.nsv", "result1688_18.nsv", "result1688_19.nsv"];
val thyn = "vfmTestDefs1688";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
