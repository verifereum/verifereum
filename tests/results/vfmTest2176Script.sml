Theory vfmTest2176[no_sig_docs]
Ancestors vfmTestDefs2176
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2176_0.nsv", "result2176_1.nsv", "result2176_2.nsv", "result2176_3.nsv", "result2176_4.nsv", "result2176_5.nsv", "result2176_6.nsv", "result2176_7.nsv", "result2176_8.nsv", "result2176_9.nsv", "result2176_10.nsv", "result2176_11.nsv", "result2176_12.nsv", "result2176_13.nsv", "result2176_14.nsv", "result2176_15.nsv", "result2176_16.nsv", "result2176_17.nsv", "result2176_18.nsv", "result2176_19.nsv", "result2176_20.nsv", "result2176_21.nsv", "result2176_22.nsv", "result2176_23.nsv", "result2176_24.nsv", "result2176_25.nsv", "result2176_26.nsv"];
val thyn = "vfmTestDefs2176";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
