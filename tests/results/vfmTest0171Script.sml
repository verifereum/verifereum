Theory vfmTest0171[no_sig_docs]
Ancestors vfmTestDefs0171
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0171_0.nsv", "result0171_1.nsv", "result0171_2.nsv", "result0171_3.nsv", "result0171_4.nsv", "result0171_5.nsv", "result0171_6.nsv", "result0171_7.nsv", "result0171_8.nsv", "result0171_9.nsv", "result0171_10.nsv", "result0171_11.nsv", "result0171_12.nsv", "result0171_13.nsv", "result0171_14.nsv", "result0171_15.nsv", "result0171_16.nsv", "result0171_17.nsv", "result0171_18.nsv", "result0171_19.nsv", "result0171_20.nsv", "result0171_21.nsv", "result0171_22.nsv", "result0171_23.nsv", "result0171_24.nsv", "result0171_25.nsv", "result0171_26.nsv", "result0171_27.nsv", "result0171_28.nsv", "result0171_29.nsv", "result0171_30.nsv", "result0171_31.nsv", "result0171_32.nsv", "result0171_33.nsv", "result0171_34.nsv", "result0171_35.nsv", "result0171_36.nsv", "result0171_37.nsv", "result0171_38.nsv", "result0171_39.nsv", "result0171_40.nsv", "result0171_41.nsv", "result0171_42.nsv", "result0171_43.nsv", "result0171_44.nsv", "result0171_45.nsv", "result0171_46.nsv", "result0171_47.nsv"];
val thyn = "vfmTestDefs0171";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
