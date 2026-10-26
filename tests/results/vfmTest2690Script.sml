Theory vfmTest2690[no_sig_docs]
Ancestors vfmTestDefs2690
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2690_0.nsv", "result2690_1.nsv", "result2690_2.nsv", "result2690_3.nsv", "result2690_4.nsv", "result2690_5.nsv", "result2690_6.nsv", "result2690_7.nsv", "result2690_8.nsv", "result2690_9.nsv"];
val thyn = "vfmTestDefs2690";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
