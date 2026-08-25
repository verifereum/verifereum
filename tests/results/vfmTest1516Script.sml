Theory vfmTest1516[no_sig_docs]
Ancestors vfmTestDefs1516
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1516_0.nsv"];
val thyn = "vfmTestDefs1516";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
