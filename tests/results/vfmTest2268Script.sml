Theory vfmTest2268[no_sig_docs]
Ancestors vfmTestDefs2268
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2268_0.nsv", "result2268_1.nsv", "result2268_2.nsv", "result2268_3.nsv", "result2268_4.nsv", "result2268_5.nsv", "result2268_6.nsv", "result2268_7.nsv", "result2268_8.nsv", "result2268_9.nsv", "result2268_10.nsv", "result2268_11.nsv", "result2268_12.nsv", "result2268_13.nsv", "result2268_14.nsv", "result2268_15.nsv", "result2268_16.nsv", "result2268_17.nsv", "result2268_18.nsv", "result2268_19.nsv", "result2268_20.nsv", "result2268_21.nsv", "result2268_22.nsv", "result2268_23.nsv", "result2268_24.nsv", "result2268_25.nsv", "result2268_26.nsv", "result2268_27.nsv", "result2268_28.nsv", "result2268_29.nsv"];
val thyn = "vfmTestDefs2268";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
