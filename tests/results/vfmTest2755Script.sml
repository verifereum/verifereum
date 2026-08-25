Theory vfmTest2755[no_sig_docs]
Ancestors vfmTestDefs2755
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2755_0.nsv", "result2755_1.nsv", "result2755_2.nsv", "result2755_3.nsv"];
val thyn = "vfmTestDefs2755";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
