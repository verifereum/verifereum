Theory vfmTest0264[no_sig_docs]
Ancestors vfmTestDefs0264
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0264_0.nsv", "result0264_1.nsv", "result0264_2.nsv", "result0264_3.nsv", "result0264_4.nsv", "result0264_5.nsv", "result0264_6.nsv", "result0264_7.nsv", "result0264_8.nsv", "result0264_9.nsv", "result0264_10.nsv", "result0264_11.nsv", "result0264_12.nsv", "result0264_13.nsv", "result0264_14.nsv", "result0264_15.nsv", "result0264_16.nsv", "result0264_17.nsv", "result0264_18.nsv", "result0264_19.nsv", "result0264_20.nsv", "result0264_21.nsv", "result0264_22.nsv", "result0264_23.nsv", "result0264_24.nsv", "result0264_25.nsv", "result0264_26.nsv", "result0264_27.nsv", "result0264_28.nsv", "result0264_29.nsv", "result0264_30.nsv", "result0264_31.nsv", "result0264_32.nsv", "result0264_33.nsv", "result0264_34.nsv", "result0264_35.nsv", "result0264_36.nsv", "result0264_37.nsv", "result0264_38.nsv", "result0264_39.nsv", "result0264_40.nsv", "result0264_41.nsv", "result0264_42.nsv", "result0264_43.nsv", "result0264_44.nsv", "result0264_45.nsv"];
val thyn = "vfmTestDefs0264";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
