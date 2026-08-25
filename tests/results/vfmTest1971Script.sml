Theory vfmTest1971[no_sig_docs]
Ancestors vfmTestDefs1971
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1971_0.nsv"];
val thyn = "vfmTestDefs1971";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
