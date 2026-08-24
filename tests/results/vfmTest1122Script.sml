Theory vfmTest1122[no_sig_docs]
Ancestors vfmTestDefs1122
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1122_0.nsv", "result1122_1.nsv", "result1122_2.nsv"];
val thyn = "vfmTestDefs1122";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
