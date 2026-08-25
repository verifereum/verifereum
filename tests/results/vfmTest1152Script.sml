Theory vfmTest1152[no_sig_docs]
Ancestors vfmTestDefs1152
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1152_0.nsv"];
val thyn = "vfmTestDefs1152";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
