Theory vfmTest1086[no_sig_docs]
Ancestors vfmTestDefs1086
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1086_0.nsv", "result1086_1.nsv", "result1086_2.nsv", "result1086_3.nsv", "result1086_4.nsv", "result1086_5.nsv", "result1086_6.nsv", "result1086_7.nsv", "result1086_8.nsv", "result1086_9.nsv", "result1086_10.nsv", "result1086_11.nsv", "result1086_12.nsv", "result1086_13.nsv", "result1086_14.nsv", "result1086_15.nsv"];
val thyn = "vfmTestDefs1086";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
