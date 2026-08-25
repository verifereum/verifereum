Theory vfmTest1441[no_sig_docs]
Ancestors vfmTestDefs1441
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1441_0.nsv"];
val thyn = "vfmTestDefs1441";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
