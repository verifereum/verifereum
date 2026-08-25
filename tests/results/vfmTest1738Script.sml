Theory vfmTest1738[no_sig_docs]
Ancestors vfmTestDefs1738
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1738_0.nsv"];
val thyn = "vfmTestDefs1738";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
