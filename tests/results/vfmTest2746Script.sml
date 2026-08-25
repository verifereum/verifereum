Theory vfmTest2746[no_sig_docs]
Ancestors vfmTestDefs2746
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2746_0.nsv", "result2746_1.nsv", "result2746_2.nsv", "result2746_3.nsv"];
val thyn = "vfmTestDefs2746";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
