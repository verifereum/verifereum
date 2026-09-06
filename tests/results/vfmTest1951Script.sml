Theory vfmTest1951[no_sig_docs]
Ancestors vfmTestDefs1951
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1951_0.nsv", "result1951_1.nsv"];
val thyn = "vfmTestDefs1951";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
