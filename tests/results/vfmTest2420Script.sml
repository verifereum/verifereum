Theory vfmTest2420[no_sig_docs]
Ancestors vfmTestDefs2420
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2420_0.nsv", "result2420_1.nsv", "result2420_2.nsv", "result2420_3.nsv", "result2420_4.nsv", "result2420_5.nsv", "result2420_6.nsv", "result2420_7.nsv", "result2420_8.nsv", "result2420_9.nsv", "result2420_10.nsv", "result2420_11.nsv"];
val thyn = "vfmTestDefs2420";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
