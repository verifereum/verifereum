Theory vfmTest2421[no_sig_docs]
Ancestors vfmTestDefs2421
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2421_0.nsv", "result2421_1.nsv"];
val thyn = "vfmTestDefs2421";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
