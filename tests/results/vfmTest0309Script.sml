Theory vfmTest0309[no_sig_docs]
Ancestors vfmTestDefs0309
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0309_0.nsv", "result0309_1.nsv", "result0309_2.nsv", "result0309_3.nsv", "result0309_4.nsv", "result0309_5.nsv", "result0309_6.nsv", "result0309_7.nsv", "result0309_8.nsv", "result0309_9.nsv", "result0309_10.nsv", "result0309_11.nsv", "result0309_12.nsv", "result0309_13.nsv", "result0309_14.nsv", "result0309_15.nsv", "result0309_16.nsv", "result0309_17.nsv", "result0309_18.nsv", "result0309_19.nsv", "result0309_20.nsv", "result0309_21.nsv", "result0309_22.nsv", "result0309_23.nsv", "result0309_24.nsv", "result0309_25.nsv", "result0309_26.nsv", "result0309_27.nsv", "result0309_28.nsv", "result0309_29.nsv", "result0309_30.nsv", "result0309_31.nsv", "result0309_32.nsv", "result0309_33.nsv", "result0309_34.nsv", "result0309_35.nsv", "result0309_36.nsv", "result0309_37.nsv", "result0309_38.nsv", "result0309_39.nsv", "result0309_40.nsv", "result0309_41.nsv", "result0309_42.nsv", "result0309_43.nsv", "result0309_44.nsv", "result0309_45.nsv", "result0309_46.nsv", "result0309_47.nsv", "result0309_48.nsv", "result0309_49.nsv", "result0309_50.nsv", "result0309_51.nsv", "result0309_52.nsv", "result0309_53.nsv", "result0309_54.nsv", "result0309_55.nsv", "result0309_56.nsv", "result0309_57.nsv", "result0309_58.nsv", "result0309_59.nsv", "result0309_60.nsv", "result0309_61.nsv"];
val thyn = "vfmTestDefs0309";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
