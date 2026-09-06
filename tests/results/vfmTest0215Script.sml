Theory vfmTest0215[no_sig_docs]
Ancestors vfmTestDefs0215
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0215_0.nsv", "result0215_1.nsv", "result0215_2.nsv", "result0215_3.nsv", "result0215_4.nsv", "result0215_5.nsv", "result0215_6.nsv", "result0215_7.nsv", "result0215_8.nsv", "result0215_9.nsv", "result0215_10.nsv", "result0215_11.nsv", "result0215_12.nsv", "result0215_13.nsv", "result0215_14.nsv", "result0215_15.nsv", "result0215_16.nsv", "result0215_17.nsv", "result0215_18.nsv", "result0215_19.nsv", "result0215_20.nsv", "result0215_21.nsv", "result0215_22.nsv", "result0215_23.nsv", "result0215_24.nsv", "result0215_25.nsv", "result0215_26.nsv", "result0215_27.nsv", "result0215_28.nsv", "result0215_29.nsv", "result0215_30.nsv", "result0215_31.nsv", "result0215_32.nsv", "result0215_33.nsv", "result0215_34.nsv", "result0215_35.nsv", "result0215_36.nsv", "result0215_37.nsv", "result0215_38.nsv", "result0215_39.nsv", "result0215_40.nsv", "result0215_41.nsv", "result0215_42.nsv", "result0215_43.nsv", "result0215_44.nsv", "result0215_45.nsv"];
val thyn = "vfmTestDefs0215";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
