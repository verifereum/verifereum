Theory vfmTest2798[no_sig_docs]
Ancestors vfmTestDefs2798
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2798_0.nsv", "result2798_1.nsv", "result2798_2.nsv", "result2798_3.nsv"];
val thyn = "vfmTestDefs2798";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
