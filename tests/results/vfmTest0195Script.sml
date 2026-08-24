Theory vfmTest0195[no_sig_docs]
Ancestors vfmTestDefs0195
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0195_0.nsv", "result0195_1.nsv", "result0195_2.nsv", "result0195_3.nsv", "result0195_4.nsv", "result0195_5.nsv", "result0195_6.nsv", "result0195_7.nsv", "result0195_8.nsv", "result0195_9.nsv", "result0195_10.nsv", "result0195_11.nsv", "result0195_12.nsv", "result0195_13.nsv", "result0195_14.nsv", "result0195_15.nsv", "result0195_16.nsv", "result0195_17.nsv", "result0195_18.nsv", "result0195_19.nsv", "result0195_20.nsv", "result0195_21.nsv", "result0195_22.nsv", "result0195_23.nsv", "result0195_24.nsv", "result0195_25.nsv", "result0195_26.nsv", "result0195_27.nsv", "result0195_28.nsv", "result0195_29.nsv", "result0195_30.nsv", "result0195_31.nsv", "result0195_32.nsv", "result0195_33.nsv", "result0195_34.nsv", "result0195_35.nsv", "result0195_36.nsv", "result0195_37.nsv", "result0195_38.nsv", "result0195_39.nsv", "result0195_40.nsv", "result0195_41.nsv", "result0195_42.nsv", "result0195_43.nsv", "result0195_44.nsv", "result0195_45.nsv"];
val thyn = "vfmTestDefs0195";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
