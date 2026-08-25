Theory vfmTest1188[no_sig_docs]
Ancestors vfmTestDefs1188
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1188_0.nsv"];
val thyn = "vfmTestDefs1188";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
