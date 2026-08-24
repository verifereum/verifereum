Theory vfmTest0977[no_sig_docs]
Ancestors vfmTestDefs0977
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0977_0.nsv", "result0977_1.nsv", "result0977_2.nsv", "result0977_3.nsv", "result0977_4.nsv", "result0977_5.nsv", "result0977_6.nsv", "result0977_7.nsv", "result0977_8.nsv", "result0977_9.nsv", "result0977_10.nsv", "result0977_11.nsv", "result0977_12.nsv", "result0977_13.nsv", "result0977_14.nsv", "result0977_15.nsv", "result0977_16.nsv", "result0977_17.nsv", "result0977_18.nsv", "result0977_19.nsv", "result0977_20.nsv", "result0977_21.nsv", "result0977_22.nsv", "result0977_23.nsv", "result0977_24.nsv", "result0977_25.nsv", "result0977_26.nsv", "result0977_27.nsv", "result0977_28.nsv", "result0977_29.nsv", "result0977_30.nsv", "result0977_31.nsv", "result0977_32.nsv", "result0977_33.nsv", "result0977_34.nsv", "result0977_35.nsv", "result0977_36.nsv", "result0977_37.nsv", "result0977_38.nsv", "result0977_39.nsv", "result0977_40.nsv", "result0977_41.nsv", "result0977_42.nsv", "result0977_43.nsv", "result0977_44.nsv", "result0977_45.nsv", "result0977_46.nsv", "result0977_47.nsv"];
val thyn = "vfmTestDefs0977";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
