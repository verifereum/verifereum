Theory vfmTest0719[no_sig_docs]
Ancestors vfmTestDefs0719
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0719_0.nsv", "result0719_1.nsv", "result0719_2.nsv", "result0719_3.nsv", "result0719_4.nsv", "result0719_5.nsv", "result0719_6.nsv", "result0719_7.nsv", "result0719_8.nsv", "result0719_9.nsv", "result0719_10.nsv", "result0719_11.nsv", "result0719_12.nsv", "result0719_13.nsv", "result0719_14.nsv", "result0719_15.nsv", "result0719_16.nsv", "result0719_17.nsv", "result0719_18.nsv", "result0719_19.nsv", "result0719_20.nsv", "result0719_21.nsv", "result0719_22.nsv", "result0719_23.nsv", "result0719_24.nsv", "result0719_25.nsv", "result0719_26.nsv", "result0719_27.nsv", "result0719_28.nsv", "result0719_29.nsv", "result0719_30.nsv", "result0719_31.nsv", "result0719_32.nsv", "result0719_33.nsv", "result0719_34.nsv", "result0719_35.nsv", "result0719_36.nsv", "result0719_37.nsv", "result0719_38.nsv", "result0719_39.nsv", "result0719_40.nsv", "result0719_41.nsv", "result0719_42.nsv", "result0719_43.nsv", "result0719_44.nsv", "result0719_45.nsv", "result0719_46.nsv", "result0719_47.nsv", "result0719_48.nsv", "result0719_49.nsv", "result0719_50.nsv", "result0719_51.nsv", "result0719_52.nsv", "result0719_53.nsv", "result0719_54.nsv"];
val thyn = "vfmTestDefs0719";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
