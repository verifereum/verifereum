Theory vfmTest2985[no_sig_docs]
Ancestors vfmTestDefs2985
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2985_0.nsv", "result2985_1.nsv", "result2985_2.nsv", "result2985_3.nsv", "result2985_4.nsv", "result2985_5.nsv", "result2985_6.nsv", "result2985_7.nsv", "result2985_8.nsv", "result2985_9.nsv", "result2985_10.nsv", "result2985_11.nsv", "result2985_12.nsv", "result2985_13.nsv", "result2985_14.nsv", "result2985_15.nsv", "result2985_16.nsv", "result2985_17.nsv", "result2985_18.nsv", "result2985_19.nsv", "result2985_20.nsv", "result2985_21.nsv", "result2985_22.nsv", "result2985_23.nsv", "result2985_24.nsv", "result2985_25.nsv", "result2985_26.nsv", "result2985_27.nsv", "result2985_28.nsv", "result2985_29.nsv", "result2985_30.nsv", "result2985_31.nsv", "result2985_32.nsv", "result2985_33.nsv", "result2985_34.nsv", "result2985_35.nsv", "result2985_36.nsv", "result2985_37.nsv", "result2985_38.nsv", "result2985_39.nsv", "result2985_40.nsv", "result2985_41.nsv", "result2985_42.nsv", "result2985_43.nsv", "result2985_44.nsv", "result2985_45.nsv", "result2985_46.nsv", "result2985_47.nsv", "result2985_48.nsv", "result2985_49.nsv", "result2985_50.nsv", "result2985_51.nsv", "result2985_52.nsv", "result2985_53.nsv"];
val thyn = "vfmTestDefs2985";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
