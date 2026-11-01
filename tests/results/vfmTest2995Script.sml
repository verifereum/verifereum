Theory vfmTest2995[no_sig_docs]
Ancestors vfmTestDefs2995
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2995_0.nsv", "result2995_1.nsv"];
val thyn = "vfmTestDefs2995";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
