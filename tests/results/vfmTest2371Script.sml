Theory vfmTest2371[no_sig_docs]
Ancestors vfmTestDefs2371
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2371_0.nsv", "result2371_1.nsv"];
val thyn = "vfmTestDefs2371";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
