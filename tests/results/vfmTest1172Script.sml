Theory vfmTest1172[no_sig_docs]
Ancestors vfmTestDefs1172
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1172_0.nsv"];
val thyn = "vfmTestDefs1172";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
