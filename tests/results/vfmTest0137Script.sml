Theory vfmTest0137[no_sig_docs]
Ancestors vfmTestDefs0137
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0137_0.nsv", "result0137_1.nsv", "result0137_2.nsv", "result0137_3.nsv", "result0137_4.nsv", "result0137_5.nsv", "result0137_6.nsv", "result0137_7.nsv", "result0137_8.nsv", "result0137_9.nsv", "result0137_10.nsv", "result0137_11.nsv", "result0137_12.nsv", "result0137_13.nsv", "result0137_14.nsv", "result0137_15.nsv", "result0137_16.nsv", "result0137_17.nsv", "result0137_18.nsv", "result0137_19.nsv", "result0137_20.nsv", "result0137_21.nsv", "result0137_22.nsv", "result0137_23.nsv", "result0137_24.nsv", "result0137_25.nsv", "result0137_26.nsv", "result0137_27.nsv", "result0137_28.nsv", "result0137_29.nsv", "result0137_30.nsv", "result0137_31.nsv", "result0137_32.nsv", "result0137_33.nsv", "result0137_34.nsv", "result0137_35.nsv", "result0137_36.nsv", "result0137_37.nsv", "result0137_38.nsv", "result0137_39.nsv", "result0137_40.nsv", "result0137_41.nsv", "result0137_42.nsv", "result0137_43.nsv", "result0137_44.nsv", "result0137_45.nsv"];
val thyn = "vfmTestDefs0137";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
