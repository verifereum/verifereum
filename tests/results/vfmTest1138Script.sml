Theory vfmTest1138[no_sig_docs]
Ancestors vfmTestDefs1138
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1138_0.nsv", "result1138_1.nsv", "result1138_2.nsv"];
val thyn = "vfmTestDefs1138";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
