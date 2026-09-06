Theory vfmTest2077[no_sig_docs]
Ancestors vfmTestDefs2077
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2077_0.nsv", "result2077_1.nsv", "result2077_2.nsv", "result2077_3.nsv", "result2077_4.nsv", "result2077_5.nsv", "result2077_6.nsv", "result2077_7.nsv"];
val thyn = "vfmTestDefs2077";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
