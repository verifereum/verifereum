Theory vfmTest1927[no_sig_docs]
Ancestors vfmTestDefs1927
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1927_0.nsv", "result1927_1.nsv"];
val thyn = "vfmTestDefs1927";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
