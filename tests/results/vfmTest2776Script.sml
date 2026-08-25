Theory vfmTest2776[no_sig_docs]
Ancestors vfmTestDefs2776
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2776_0.nsv", "result2776_1.nsv", "result2776_2.nsv", "result2776_3.nsv"];
val thyn = "vfmTestDefs2776";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
