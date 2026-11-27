Theory vfmTest0339[no_sig_docs]
Ancestors vfmTestDefs0339
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0339_0.nsv", "result0339_1.nsv", "result0339_2.nsv", "result0339_3.nsv", "result0339_4.nsv", "result0339_5.nsv", "result0339_6.nsv", "result0339_7.nsv", "result0339_8.nsv", "result0339_9.nsv", "result0339_10.nsv", "result0339_11.nsv", "result0339_12.nsv", "result0339_13.nsv", "result0339_14.nsv", "result0339_15.nsv", "result0339_16.nsv", "result0339_17.nsv", "result0339_18.nsv", "result0339_19.nsv", "result0339_20.nsv", "result0339_21.nsv", "result0339_22.nsv", "result0339_23.nsv", "result0339_24.nsv", "result0339_25.nsv", "result0339_26.nsv", "result0339_27.nsv", "result0339_28.nsv", "result0339_29.nsv", "result0339_30.nsv", "result0339_31.nsv", "result0339_32.nsv", "result0339_33.nsv", "result0339_34.nsv", "result0339_35.nsv", "result0339_36.nsv", "result0339_37.nsv", "result0339_38.nsv", "result0339_39.nsv", "result0339_40.nsv", "result0339_41.nsv", "result0339_42.nsv", "result0339_43.nsv", "result0339_44.nsv", "result0339_45.nsv", "result0339_46.nsv", "result0339_47.nsv", "result0339_48.nsv", "result0339_49.nsv", "result0339_50.nsv", "result0339_51.nsv", "result0339_52.nsv", "result0339_53.nsv", "result0339_54.nsv", "result0339_55.nsv"];
val thyn = "vfmTestDefs0339";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
