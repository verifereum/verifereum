Theory vfmTest1069[no_sig_docs]
Ancestors vfmTestDefs1069
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1069_0.nsv", "result1069_1.nsv", "result1069_2.nsv", "result1069_3.nsv"];
val thyn = "vfmTestDefs1069";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
