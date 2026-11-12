Theory vfmTest0602[no_sig_docs]
Ancestors vfmTestDefs0602
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0602_0.nsv", "result0602_1.nsv", "result0602_2.nsv", "result0602_3.nsv", "result0602_4.nsv", "result0602_5.nsv", "result0602_6.nsv", "result0602_7.nsv", "result0602_8.nsv", "result0602_9.nsv", "result0602_10.nsv", "result0602_11.nsv", "result0602_12.nsv", "result0602_13.nsv", "result0602_14.nsv", "result0602_15.nsv", "result0602_16.nsv", "result0602_17.nsv", "result0602_18.nsv", "result0602_19.nsv", "result0602_20.nsv", "result0602_21.nsv", "result0602_22.nsv", "result0602_23.nsv", "result0602_24.nsv", "result0602_25.nsv", "result0602_26.nsv", "result0602_27.nsv", "result0602_28.nsv", "result0602_29.nsv", "result0602_30.nsv", "result0602_31.nsv", "result0602_32.nsv", "result0602_33.nsv", "result0602_34.nsv", "result0602_35.nsv", "result0602_36.nsv", "result0602_37.nsv", "result0602_38.nsv", "result0602_39.nsv", "result0602_40.nsv", "result0602_41.nsv", "result0602_42.nsv", "result0602_43.nsv", "result0602_44.nsv", "result0602_45.nsv", "result0602_46.nsv", "result0602_47.nsv", "result0602_48.nsv", "result0602_49.nsv", "result0602_50.nsv", "result0602_51.nsv", "result0602_52.nsv", "result0602_53.nsv", "result0602_54.nsv"];
val thyn = "vfmTestDefs0602";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
