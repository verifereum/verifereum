Theory vfmTest2122[no_sig_docs]
Ancestors vfmTestDefs2122
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2122_0.nsv", "result2122_1.nsv", "result2122_2.nsv", "result2122_3.nsv", "result2122_4.nsv", "result2122_5.nsv", "result2122_6.nsv", "result2122_7.nsv", "result2122_8.nsv", "result2122_9.nsv"];
val thyn = "vfmTestDefs2122";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
