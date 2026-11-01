Theory vfmTest1091[no_sig_docs]
Ancestors vfmTestDefs1091
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1091_0.nsv", "result1091_1.nsv", "result1091_2.nsv", "result1091_3.nsv", "result1091_4.nsv", "result1091_5.nsv", "result1091_6.nsv", "result1091_7.nsv", "result1091_8.nsv", "result1091_9.nsv", "result1091_10.nsv", "result1091_11.nsv", "result1091_12.nsv", "result1091_13.nsv", "result1091_14.nsv", "result1091_15.nsv", "result1091_16.nsv", "result1091_17.nsv"];
val thyn = "vfmTestDefs1091";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
