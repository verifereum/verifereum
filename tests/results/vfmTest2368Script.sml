Theory vfmTest2368[no_sig_docs]
Ancestors vfmTestDefs2368
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2368_0.nsv", "result2368_1.nsv"];
val thyn = "vfmTestDefs2368";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
