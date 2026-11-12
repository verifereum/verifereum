Theory vfmTest2106[no_sig_docs]
Ancestors vfmTestDefs2106
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2106_0.nsv", "result2106_1.nsv", "result2106_2.nsv", "result2106_3.nsv", "result2106_4.nsv", "result2106_5.nsv", "result2106_6.nsv", "result2106_7.nsv", "result2106_8.nsv", "result2106_9.nsv", "result2106_10.nsv", "result2106_11.nsv", "result2106_12.nsv", "result2106_13.nsv", "result2106_14.nsv", "result2106_15.nsv", "result2106_16.nsv", "result2106_17.nsv", "result2106_18.nsv", "result2106_19.nsv", "result2106_20.nsv", "result2106_21.nsv", "result2106_22.nsv", "result2106_23.nsv", "result2106_24.nsv", "result2106_25.nsv"];
val thyn = "vfmTestDefs2106";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
