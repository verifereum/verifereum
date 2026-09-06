Theory vfmTest2273[no_sig_docs]
Ancestors vfmTestDefs2273
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2273_0.nsv", "result2273_1.nsv", "result2273_2.nsv", "result2273_3.nsv", "result2273_4.nsv", "result2273_5.nsv", "result2273_6.nsv", "result2273_7.nsv", "result2273_8.nsv", "result2273_9.nsv", "result2273_10.nsv", "result2273_11.nsv", "result2273_12.nsv", "result2273_13.nsv", "result2273_14.nsv", "result2273_15.nsv", "result2273_16.nsv", "result2273_17.nsv", "result2273_18.nsv", "result2273_19.nsv", "result2273_20.nsv", "result2273_21.nsv", "result2273_22.nsv", "result2273_23.nsv", "result2273_24.nsv", "result2273_25.nsv", "result2273_26.nsv", "result2273_27.nsv", "result2273_28.nsv", "result2273_29.nsv", "result2273_30.nsv", "result2273_31.nsv", "result2273_32.nsv", "result2273_33.nsv", "result2273_34.nsv", "result2273_35.nsv"];
val thyn = "vfmTestDefs2273";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
