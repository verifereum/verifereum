Theory vfmTest2739[no_sig_docs]
Ancestors vfmTestDefs2739
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2739_0.nsv", "result2739_1.nsv", "result2739_2.nsv", "result2739_3.nsv"];
val thyn = "vfmTestDefs2739";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
