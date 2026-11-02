Theory vfmTest1143[no_sig_docs]
Ancestors vfmTestDefs1143
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1143_0.nsv", "result1143_1.nsv"];
val thyn = "vfmTestDefs1143";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
