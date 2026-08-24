Theory vfmTest2324[no_sig_docs]
Ancestors vfmTestDefs2324
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2324_0.nsv", "result2324_1.nsv"];
val thyn = "vfmTestDefs2324";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
