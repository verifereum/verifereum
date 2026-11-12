Theory vfmTest2197[no_sig_docs]
Ancestors vfmTestDefs2197
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2197_0.nsv", "result2197_1.nsv", "result2197_2.nsv", "result2197_3.nsv", "result2197_4.nsv", "result2197_5.nsv", "result2197_6.nsv", "result2197_7.nsv"];
val thyn = "vfmTestDefs2197";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
