Theory vfmTest0267[no_sig_docs]
Ancestors vfmTestDefs0267
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0267_0.nsv", "result0267_1.nsv", "result0267_2.nsv", "result0267_3.nsv", "result0267_4.nsv", "result0267_5.nsv", "result0267_6.nsv", "result0267_7.nsv", "result0267_8.nsv", "result0267_9.nsv", "result0267_10.nsv", "result0267_11.nsv", "result0267_12.nsv", "result0267_13.nsv", "result0267_14.nsv", "result0267_15.nsv", "result0267_16.nsv", "result0267_17.nsv", "result0267_18.nsv", "result0267_19.nsv", "result0267_20.nsv", "result0267_21.nsv", "result0267_22.nsv", "result0267_23.nsv", "result0267_24.nsv", "result0267_25.nsv", "result0267_26.nsv", "result0267_27.nsv", "result0267_28.nsv", "result0267_29.nsv", "result0267_30.nsv", "result0267_31.nsv", "result0267_32.nsv", "result0267_33.nsv", "result0267_34.nsv", "result0267_35.nsv", "result0267_36.nsv", "result0267_37.nsv", "result0267_38.nsv", "result0267_39.nsv", "result0267_40.nsv", "result0267_41.nsv", "result0267_42.nsv", "result0267_43.nsv", "result0267_44.nsv", "result0267_45.nsv", "result0267_46.nsv", "result0267_47.nsv", "result0267_48.nsv", "result0267_49.nsv", "result0267_50.nsv", "result0267_51.nsv", "result0267_52.nsv", "result0267_53.nsv", "result0267_54.nsv", "result0267_55.nsv"];
val thyn = "vfmTestDefs0267";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
