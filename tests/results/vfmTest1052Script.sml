Theory vfmTest1052[no_sig_docs]
Ancestors vfmTestDefs1052
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1052_0.nsv", "result1052_1.nsv", "result1052_2.nsv", "result1052_3.nsv", "result1052_4.nsv", "result1052_5.nsv", "result1052_6.nsv", "result1052_7.nsv", "result1052_8.nsv"];
val thyn = "vfmTestDefs1052";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
