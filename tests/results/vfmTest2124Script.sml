Theory vfmTest2124[no_sig_docs]
Ancestors vfmTestDefs2124
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2124_0.nsv", "result2124_1.nsv", "result2124_2.nsv", "result2124_3.nsv", "result2124_4.nsv", "result2124_5.nsv", "result2124_6.nsv", "result2124_7.nsv", "result2124_8.nsv", "result2124_9.nsv", "result2124_10.nsv", "result2124_11.nsv", "result2124_12.nsv", "result2124_13.nsv", "result2124_14.nsv", "result2124_15.nsv", "result2124_16.nsv"];
val thyn = "vfmTestDefs2124";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
