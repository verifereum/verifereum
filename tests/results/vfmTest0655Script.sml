Theory vfmTest0655[no_sig_docs]
Ancestors vfmTestDefs0655
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0655_0.nsv", "result0655_1.nsv", "result0655_2.nsv", "result0655_3.nsv", "result0655_4.nsv", "result0655_5.nsv", "result0655_6.nsv", "result0655_7.nsv", "result0655_8.nsv", "result0655_9.nsv", "result0655_10.nsv", "result0655_11.nsv", "result0655_12.nsv", "result0655_13.nsv", "result0655_14.nsv", "result0655_15.nsv", "result0655_16.nsv", "result0655_17.nsv", "result0655_18.nsv", "result0655_19.nsv", "result0655_20.nsv", "result0655_21.nsv", "result0655_22.nsv", "result0655_23.nsv", "result0655_24.nsv", "result0655_25.nsv", "result0655_26.nsv", "result0655_27.nsv", "result0655_28.nsv", "result0655_29.nsv", "result0655_30.nsv", "result0655_31.nsv", "result0655_32.nsv", "result0655_33.nsv", "result0655_34.nsv", "result0655_35.nsv", "result0655_36.nsv", "result0655_37.nsv", "result0655_38.nsv", "result0655_39.nsv", "result0655_40.nsv", "result0655_41.nsv", "result0655_42.nsv", "result0655_43.nsv", "result0655_44.nsv", "result0655_45.nsv", "result0655_46.nsv", "result0655_47.nsv"];
val thyn = "vfmTestDefs0655";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
