Theory vfmTest1063[no_sig_docs]
Ancestors vfmTestDefs1063
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1063_0.nsv", "result1063_1.nsv"];
val thyn = "vfmTestDefs1063";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
