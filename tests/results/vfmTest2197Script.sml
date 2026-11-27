Theory vfmTest2197[no_sig_docs]
Ancestors vfmTestDefs2197
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2197_0.nsv", "result2197_1.nsv", "result2197_2.nsv", "result2197_3.nsv", "result2197_4.nsv", "result2197_5.nsv", "result2197_6.nsv", "result2197_7.nsv", "result2197_8.nsv", "result2197_9.nsv", "result2197_10.nsv", "result2197_11.nsv", "result2197_12.nsv", "result2197_13.nsv", "result2197_14.nsv", "result2197_15.nsv", "result2197_16.nsv", "result2197_17.nsv", "result2197_18.nsv", "result2197_19.nsv", "result2197_20.nsv", "result2197_21.nsv", "result2197_22.nsv", "result2197_23.nsv", "result2197_24.nsv", "result2197_25.nsv", "result2197_26.nsv", "result2197_27.nsv", "result2197_28.nsv", "result2197_29.nsv", "result2197_30.nsv", "result2197_31.nsv", "result2197_32.nsv", "result2197_33.nsv", "result2197_34.nsv"];
val thyn = "vfmTestDefs2197";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
