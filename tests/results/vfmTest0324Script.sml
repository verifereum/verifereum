Theory vfmTest0324[no_sig_docs]
Ancestors vfmTestDefs0324
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0324_0.nsv", "result0324_1.nsv", "result0324_2.nsv", "result0324_3.nsv", "result0324_4.nsv", "result0324_5.nsv", "result0324_6.nsv", "result0324_7.nsv", "result0324_8.nsv", "result0324_9.nsv", "result0324_10.nsv", "result0324_11.nsv", "result0324_12.nsv", "result0324_13.nsv", "result0324_14.nsv", "result0324_15.nsv", "result0324_16.nsv", "result0324_17.nsv", "result0324_18.nsv", "result0324_19.nsv", "result0324_20.nsv", "result0324_21.nsv", "result0324_22.nsv", "result0324_23.nsv", "result0324_24.nsv", "result0324_25.nsv", "result0324_26.nsv", "result0324_27.nsv", "result0324_28.nsv", "result0324_29.nsv", "result0324_30.nsv", "result0324_31.nsv", "result0324_32.nsv", "result0324_33.nsv", "result0324_34.nsv", "result0324_35.nsv", "result0324_36.nsv", "result0324_37.nsv", "result0324_38.nsv", "result0324_39.nsv", "result0324_40.nsv", "result0324_41.nsv", "result0324_42.nsv", "result0324_43.nsv", "result0324_44.nsv", "result0324_45.nsv", "result0324_46.nsv", "result0324_47.nsv", "result0324_48.nsv", "result0324_49.nsv", "result0324_50.nsv", "result0324_51.nsv", "result0324_52.nsv", "result0324_53.nsv", "result0324_54.nsv", "result0324_55.nsv"];
val thyn = "vfmTestDefs0324";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
