Theory vfmTest1219[no_sig_docs]
Ancestors vfmTestDefs1219
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1219_0.nsv"];
val thyn = "vfmTestDefs1219";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
