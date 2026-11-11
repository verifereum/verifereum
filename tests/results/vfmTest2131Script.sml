Theory vfmTest2131[no_sig_docs]
Ancestors vfmTestDefs2131
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2131_0.nsv", "result2131_1.nsv", "result2131_2.nsv", "result2131_3.nsv", "result2131_4.nsv", "result2131_5.nsv", "result2131_6.nsv", "result2131_7.nsv", "result2131_8.nsv", "result2131_9.nsv", "result2131_10.nsv", "result2131_11.nsv", "result2131_12.nsv", "result2131_13.nsv", "result2131_14.nsv", "result2131_15.nsv", "result2131_16.nsv", "result2131_17.nsv", "result2131_18.nsv", "result2131_19.nsv", "result2131_20.nsv", "result2131_21.nsv", "result2131_22.nsv", "result2131_23.nsv", "result2131_24.nsv", "result2131_25.nsv", "result2131_26.nsv", "result2131_27.nsv", "result2131_28.nsv", "result2131_29.nsv", "result2131_30.nsv", "result2131_31.nsv"];
val thyn = "vfmTestDefs2131";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
