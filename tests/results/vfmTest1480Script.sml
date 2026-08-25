Theory vfmTest1480[no_sig_docs]
Ancestors vfmTestDefs1480
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1480_0.nsv"];
val thyn = "vfmTestDefs1480";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
