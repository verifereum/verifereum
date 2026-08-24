Theory vfmTest0200[no_sig_docs]
Ancestors vfmTestDefs0200
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0200_0.nsv", "result0200_1.nsv", "result0200_2.nsv", "result0200_3.nsv", "result0200_4.nsv", "result0200_5.nsv", "result0200_6.nsv", "result0200_7.nsv", "result0200_8.nsv", "result0200_9.nsv", "result0200_10.nsv", "result0200_11.nsv", "result0200_12.nsv", "result0200_13.nsv", "result0200_14.nsv", "result0200_15.nsv", "result0200_16.nsv", "result0200_17.nsv", "result0200_18.nsv", "result0200_19.nsv", "result0200_20.nsv", "result0200_21.nsv", "result0200_22.nsv", "result0200_23.nsv", "result0200_24.nsv", "result0200_25.nsv", "result0200_26.nsv", "result0200_27.nsv", "result0200_28.nsv", "result0200_29.nsv", "result0200_30.nsv", "result0200_31.nsv", "result0200_32.nsv", "result0200_33.nsv", "result0200_34.nsv", "result0200_35.nsv", "result0200_36.nsv", "result0200_37.nsv", "result0200_38.nsv", "result0200_39.nsv", "result0200_40.nsv", "result0200_41.nsv", "result0200_42.nsv", "result0200_43.nsv", "result0200_44.nsv", "result0200_45.nsv", "result0200_46.nsv", "result0200_47.nsv", "result0200_48.nsv", "result0200_49.nsv", "result0200_50.nsv", "result0200_51.nsv", "result0200_52.nsv", "result0200_53.nsv", "result0200_54.nsv", "result0200_55.nsv"];
val thyn = "vfmTestDefs0200";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
