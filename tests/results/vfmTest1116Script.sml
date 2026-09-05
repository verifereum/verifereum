Theory vfmTest1116[no_sig_docs]
Ancestors vfmTestDefs1116
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1116_0.nsv"];
val thyn = "vfmTestDefs1116";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
