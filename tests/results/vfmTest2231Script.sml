Theory vfmTest2231[no_sig_docs]
Ancestors vfmTestDefs2231
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2231_0.nsv", "result2231_1.nsv", "result2231_2.nsv", "result2231_3.nsv", "result2231_4.nsv", "result2231_5.nsv", "result2231_6.nsv", "result2231_7.nsv", "result2231_8.nsv", "result2231_9.nsv", "result2231_10.nsv", "result2231_11.nsv", "result2231_12.nsv", "result2231_13.nsv", "result2231_14.nsv", "result2231_15.nsv", "result2231_16.nsv"];
val thyn = "vfmTestDefs2231";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
