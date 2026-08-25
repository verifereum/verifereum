Theory vfmTest0237[no_sig_docs]
Ancestors vfmTestDefs0237
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0237_0.nsv", "result0237_1.nsv", "result0237_2.nsv", "result0237_3.nsv", "result0237_4.nsv", "result0237_5.nsv", "result0237_6.nsv", "result0237_7.nsv", "result0237_8.nsv", "result0237_9.nsv", "result0237_10.nsv", "result0237_11.nsv", "result0237_12.nsv", "result0237_13.nsv", "result0237_14.nsv", "result0237_15.nsv", "result0237_16.nsv", "result0237_17.nsv", "result0237_18.nsv", "result0237_19.nsv", "result0237_20.nsv", "result0237_21.nsv", "result0237_22.nsv", "result0237_23.nsv", "result0237_24.nsv", "result0237_25.nsv", "result0237_26.nsv", "result0237_27.nsv", "result0237_28.nsv", "result0237_29.nsv", "result0237_30.nsv", "result0237_31.nsv", "result0237_32.nsv", "result0237_33.nsv", "result0237_34.nsv", "result0237_35.nsv", "result0237_36.nsv", "result0237_37.nsv", "result0237_38.nsv", "result0237_39.nsv", "result0237_40.nsv", "result0237_41.nsv", "result0237_42.nsv", "result0237_43.nsv", "result0237_44.nsv"];
val thyn = "vfmTestDefs0237";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
