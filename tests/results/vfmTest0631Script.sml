Theory vfmTest0631[no_sig_docs]
Ancestors vfmTestDefs0631
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0631_0.nsv", "result0631_1.nsv", "result0631_2.nsv", "result0631_3.nsv", "result0631_4.nsv", "result0631_5.nsv", "result0631_6.nsv", "result0631_7.nsv", "result0631_8.nsv", "result0631_9.nsv", "result0631_10.nsv", "result0631_11.nsv", "result0631_12.nsv", "result0631_13.nsv", "result0631_14.nsv", "result0631_15.nsv", "result0631_16.nsv", "result0631_17.nsv", "result0631_18.nsv", "result0631_19.nsv", "result0631_20.nsv", "result0631_21.nsv", "result0631_22.nsv", "result0631_23.nsv", "result0631_24.nsv", "result0631_25.nsv", "result0631_26.nsv", "result0631_27.nsv", "result0631_28.nsv", "result0631_29.nsv", "result0631_30.nsv", "result0631_31.nsv", "result0631_32.nsv", "result0631_33.nsv", "result0631_34.nsv", "result0631_35.nsv", "result0631_36.nsv", "result0631_37.nsv", "result0631_38.nsv", "result0631_39.nsv", "result0631_40.nsv", "result0631_41.nsv", "result0631_42.nsv", "result0631_43.nsv", "result0631_44.nsv", "result0631_45.nsv", "result0631_46.nsv", "result0631_47.nsv"];
val thyn = "vfmTestDefs0631";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
