Theory vfmTest1311[no_sig_docs]
Ancestors vfmTestDefs1311
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1311_0.nsv"];
val thyn = "vfmTestDefs1311";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
