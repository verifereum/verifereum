Theory vfmTest2139[no_sig_docs]
Ancestors vfmTestDefs2139
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2139_0.nsv", "result2139_1.nsv", "result2139_2.nsv", "result2139_3.nsv", "result2139_4.nsv", "result2139_5.nsv", "result2139_6.nsv", "result2139_7.nsv", "result2139_8.nsv", "result2139_9.nsv", "result2139_10.nsv", "result2139_11.nsv", "result2139_12.nsv", "result2139_13.nsv", "result2139_14.nsv", "result2139_15.nsv", "result2139_16.nsv", "result2139_17.nsv", "result2139_18.nsv", "result2139_19.nsv", "result2139_20.nsv", "result2139_21.nsv", "result2139_22.nsv", "result2139_23.nsv", "result2139_24.nsv", "result2139_25.nsv", "result2139_26.nsv", "result2139_27.nsv", "result2139_28.nsv", "result2139_29.nsv", "result2139_30.nsv", "result2139_31.nsv", "result2139_32.nsv", "result2139_33.nsv", "result2139_34.nsv", "result2139_35.nsv", "result2139_36.nsv", "result2139_37.nsv", "result2139_38.nsv", "result2139_39.nsv", "result2139_40.nsv", "result2139_41.nsv", "result2139_42.nsv", "result2139_43.nsv", "result2139_44.nsv", "result2139_45.nsv", "result2139_46.nsv", "result2139_47.nsv", "result2139_48.nsv", "result2139_49.nsv", "result2139_50.nsv", "result2139_51.nsv", "result2139_52.nsv"];
val thyn = "vfmTestDefs2139";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
