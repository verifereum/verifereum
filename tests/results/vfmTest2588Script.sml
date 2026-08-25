Theory vfmTest2588[no_sig_docs]
Ancestors vfmTestDefs2588
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2588_0.nsv", "result2588_1.nsv", "result2588_2.nsv", "result2588_3.nsv"];
val thyn = "vfmTestDefs2588";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
