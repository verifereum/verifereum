Theory vfmTest1142[no_sig_docs]
Ancestors vfmTestDefs1142
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1142_0.nsv", "result1142_1.nsv"];
val thyn = "vfmTestDefs1142";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
