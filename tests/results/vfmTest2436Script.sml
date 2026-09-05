Theory vfmTest2436[no_sig_docs]
Ancestors vfmTestDefs2436
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2436_0.nsv", "result2436_1.nsv", "result2436_2.nsv", "result2436_3.nsv"];
val thyn = "vfmTestDefs2436";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
