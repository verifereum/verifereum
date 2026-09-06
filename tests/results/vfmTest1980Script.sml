Theory vfmTest1980[no_sig_docs]
Ancestors vfmTestDefs1980
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1980_0.nsv", "result1980_1.nsv"];
val thyn = "vfmTestDefs1980";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
