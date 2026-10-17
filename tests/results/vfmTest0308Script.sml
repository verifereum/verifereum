Theory vfmTest0308[no_sig_docs]
Ancestors vfmTestDefs0308
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0308_0.nsv", "result0308_1.nsv", "result0308_2.nsv", "result0308_3.nsv", "result0308_4.nsv", "result0308_5.nsv", "result0308_6.nsv", "result0308_7.nsv", "result0308_8.nsv", "result0308_9.nsv", "result0308_10.nsv", "result0308_11.nsv", "result0308_12.nsv", "result0308_13.nsv", "result0308_14.nsv", "result0308_15.nsv", "result0308_16.nsv", "result0308_17.nsv", "result0308_18.nsv", "result0308_19.nsv", "result0308_20.nsv", "result0308_21.nsv", "result0308_22.nsv", "result0308_23.nsv", "result0308_24.nsv", "result0308_25.nsv", "result0308_26.nsv", "result0308_27.nsv", "result0308_28.nsv", "result0308_29.nsv", "result0308_30.nsv", "result0308_31.nsv", "result0308_32.nsv", "result0308_33.nsv", "result0308_34.nsv", "result0308_35.nsv", "result0308_36.nsv", "result0308_37.nsv", "result0308_38.nsv", "result0308_39.nsv", "result0308_40.nsv", "result0308_41.nsv", "result0308_42.nsv", "result0308_43.nsv", "result0308_44.nsv", "result0308_45.nsv", "result0308_46.nsv", "result0308_47.nsv", "result0308_48.nsv", "result0308_49.nsv", "result0308_50.nsv", "result0308_51.nsv"];
val thyn = "vfmTestDefs0308";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
