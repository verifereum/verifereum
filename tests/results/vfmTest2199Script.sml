Theory vfmTest2199[no_sig_docs]
Ancestors vfmTestDefs2199
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2199_0.nsv", "result2199_1.nsv", "result2199_2.nsv", "result2199_3.nsv", "result2199_4.nsv", "result2199_5.nsv"];
val thyn = "vfmTestDefs2199";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
