Theory vfmTest2593[no_sig_docs]
Ancestors vfmTestDefs2593
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2593_0.nsv", "result2593_1.nsv", "result2593_2.nsv", "result2593_3.nsv"];
val thyn = "vfmTestDefs2593";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
