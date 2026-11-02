Theory vfmTest2970[no_sig_docs]
Ancestors vfmTestDefs2970
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2970_0.nsv", "result2970_1.nsv", "result2970_2.nsv", "result2970_3.nsv", "result2970_4.nsv", "result2970_5.nsv", "result2970_6.nsv", "result2970_7.nsv", "result2970_8.nsv", "result2970_9.nsv"];
val thyn = "vfmTestDefs2970";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
