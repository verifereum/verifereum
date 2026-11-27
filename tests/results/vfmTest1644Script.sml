Theory vfmTest1644[no_sig_docs]
Ancestors vfmTestDefs1644
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1644_0.nsv"];
val thyn = "vfmTestDefs1644";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
