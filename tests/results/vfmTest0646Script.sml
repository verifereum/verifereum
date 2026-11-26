Theory vfmTest0646[no_sig_docs]
Ancestors vfmTestDefs0646
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0646_0.nsv", "result0646_1.nsv", "result0646_2.nsv", "result0646_3.nsv", "result0646_4.nsv", "result0646_5.nsv", "result0646_6.nsv", "result0646_7.nsv", "result0646_8.nsv", "result0646_9.nsv", "result0646_10.nsv", "result0646_11.nsv", "result0646_12.nsv", "result0646_13.nsv", "result0646_14.nsv", "result0646_15.nsv", "result0646_16.nsv", "result0646_17.nsv", "result0646_18.nsv", "result0646_19.nsv", "result0646_20.nsv", "result0646_21.nsv", "result0646_22.nsv", "result0646_23.nsv", "result0646_24.nsv", "result0646_25.nsv", "result0646_26.nsv", "result0646_27.nsv", "result0646_28.nsv", "result0646_29.nsv", "result0646_30.nsv", "result0646_31.nsv", "result0646_32.nsv", "result0646_33.nsv", "result0646_34.nsv", "result0646_35.nsv", "result0646_36.nsv", "result0646_37.nsv", "result0646_38.nsv", "result0646_39.nsv", "result0646_40.nsv", "result0646_41.nsv", "result0646_42.nsv", "result0646_43.nsv", "result0646_44.nsv", "result0646_45.nsv", "result0646_46.nsv", "result0646_47.nsv"];
val thyn = "vfmTestDefs0646";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
