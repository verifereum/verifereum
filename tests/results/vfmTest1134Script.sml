Theory vfmTest1134[no_sig_docs]
Ancestors vfmTestDefs1134
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1134_0.nsv", "result1134_1.nsv"];
val thyn = "vfmTestDefs1134";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
