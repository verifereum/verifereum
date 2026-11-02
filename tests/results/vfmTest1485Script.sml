Theory vfmTest1485[no_sig_docs]
Ancestors vfmTestDefs1485
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1485_0.nsv", "result1485_1.nsv", "result1485_2.nsv", "result1485_3.nsv", "result1485_4.nsv", "result1485_5.nsv", "result1485_6.nsv", "result1485_7.nsv", "result1485_8.nsv", "result1485_9.nsv", "result1485_10.nsv", "result1485_11.nsv", "result1485_12.nsv", "result1485_13.nsv", "result1485_14.nsv", "result1485_15.nsv", "result1485_16.nsv", "result1485_17.nsv", "result1485_18.nsv", "result1485_19.nsv", "result1485_20.nsv", "result1485_21.nsv", "result1485_22.nsv", "result1485_23.nsv", "result1485_24.nsv", "result1485_25.nsv", "result1485_26.nsv", "result1485_27.nsv", "result1485_28.nsv", "result1485_29.nsv", "result1485_30.nsv", "result1485_31.nsv", "result1485_32.nsv", "result1485_33.nsv", "result1485_34.nsv", "result1485_35.nsv", "result1485_36.nsv", "result1485_37.nsv", "result1485_38.nsv", "result1485_39.nsv", "result1485_40.nsv", "result1485_41.nsv", "result1485_42.nsv", "result1485_43.nsv", "result1485_44.nsv", "result1485_45.nsv", "result1485_46.nsv", "result1485_47.nsv"];
val thyn = "vfmTestDefs1485";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
