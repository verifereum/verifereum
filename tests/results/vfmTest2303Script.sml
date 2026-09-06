Theory vfmTest2303[no_sig_docs]
Ancestors vfmTestDefs2303
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2303_0.nsv", "result2303_1.nsv", "result2303_2.nsv", "result2303_3.nsv", "result2303_4.nsv", "result2303_5.nsv", "result2303_6.nsv", "result2303_7.nsv", "result2303_8.nsv", "result2303_9.nsv", "result2303_10.nsv", "result2303_11.nsv", "result2303_12.nsv", "result2303_13.nsv", "result2303_14.nsv", "result2303_15.nsv", "result2303_16.nsv", "result2303_17.nsv", "result2303_18.nsv", "result2303_19.nsv", "result2303_20.nsv", "result2303_21.nsv", "result2303_22.nsv", "result2303_23.nsv", "result2303_24.nsv", "result2303_25.nsv", "result2303_26.nsv", "result2303_27.nsv", "result2303_28.nsv", "result2303_29.nsv", "result2303_30.nsv", "result2303_31.nsv", "result2303_32.nsv", "result2303_33.nsv", "result2303_34.nsv", "result2303_35.nsv", "result2303_36.nsv", "result2303_37.nsv", "result2303_38.nsv", "result2303_39.nsv", "result2303_40.nsv", "result2303_41.nsv", "result2303_42.nsv", "result2303_43.nsv", "result2303_44.nsv", "result2303_45.nsv", "result2303_46.nsv", "result2303_47.nsv", "result2303_48.nsv", "result2303_49.nsv", "result2303_50.nsv", "result2303_51.nsv", "result2303_52.nsv", "result2303_53.nsv"];
val thyn = "vfmTestDefs2303";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
