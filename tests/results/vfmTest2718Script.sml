Theory vfmTest2718[no_sig_docs]
Ancestors vfmTestDefs2718
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2718_0.nsv", "result2718_1.nsv", "result2718_2.nsv", "result2718_3.nsv"];
val thyn = "vfmTestDefs2718";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
