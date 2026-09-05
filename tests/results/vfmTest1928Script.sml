Theory vfmTest1928[no_sig_docs]
Ancestors vfmTestDefs1928
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1928_0.nsv", "result1928_1.nsv"];
val thyn = "vfmTestDefs1928";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
