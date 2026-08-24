Theory vfmTest0232[no_sig_docs]
Ancestors vfmTestDefs0232
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0232_0.nsv", "result0232_1.nsv", "result0232_2.nsv", "result0232_3.nsv", "result0232_4.nsv", "result0232_5.nsv", "result0232_6.nsv", "result0232_7.nsv", "result0232_8.nsv", "result0232_9.nsv", "result0232_10.nsv", "result0232_11.nsv", "result0232_12.nsv", "result0232_13.nsv", "result0232_14.nsv", "result0232_15.nsv", "result0232_16.nsv", "result0232_17.nsv", "result0232_18.nsv", "result0232_19.nsv", "result0232_20.nsv", "result0232_21.nsv", "result0232_22.nsv", "result0232_23.nsv", "result0232_24.nsv", "result0232_25.nsv", "result0232_26.nsv", "result0232_27.nsv", "result0232_28.nsv", "result0232_29.nsv", "result0232_30.nsv", "result0232_31.nsv", "result0232_32.nsv", "result0232_33.nsv", "result0232_34.nsv", "result0232_35.nsv", "result0232_36.nsv", "result0232_37.nsv", "result0232_38.nsv", "result0232_39.nsv", "result0232_40.nsv", "result0232_41.nsv", "result0232_42.nsv", "result0232_43.nsv", "result0232_44.nsv", "result0232_45.nsv", "result0232_46.nsv", "result0232_47.nsv", "result0232_48.nsv", "result0232_49.nsv", "result0232_50.nsv", "result0232_51.nsv", "result0232_52.nsv", "result0232_53.nsv", "result0232_54.nsv", "result0232_55.nsv", "result0232_56.nsv", "result0232_57.nsv", "result0232_58.nsv", "result0232_59.nsv", "result0232_60.nsv", "result0232_61.nsv"];
val thyn = "vfmTestDefs0232";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
