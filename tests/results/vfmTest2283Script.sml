Theory vfmTest2283[no_sig_docs]
Ancestors vfmTestDefs2283
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2283_0.nsv", "result2283_1.nsv", "result2283_2.nsv", "result2283_3.nsv", "result2283_4.nsv", "result2283_5.nsv", "result2283_6.nsv", "result2283_7.nsv", "result2283_8.nsv", "result2283_9.nsv", "result2283_10.nsv", "result2283_11.nsv", "result2283_12.nsv", "result2283_13.nsv", "result2283_14.nsv", "result2283_15.nsv", "result2283_16.nsv", "result2283_17.nsv", "result2283_18.nsv", "result2283_19.nsv", "result2283_20.nsv", "result2283_21.nsv", "result2283_22.nsv", "result2283_23.nsv", "result2283_24.nsv", "result2283_25.nsv", "result2283_26.nsv", "result2283_27.nsv", "result2283_28.nsv", "result2283_29.nsv", "result2283_30.nsv", "result2283_31.nsv", "result2283_32.nsv", "result2283_33.nsv", "result2283_34.nsv", "result2283_35.nsv", "result2283_36.nsv", "result2283_37.nsv", "result2283_38.nsv", "result2283_39.nsv", "result2283_40.nsv", "result2283_41.nsv", "result2283_42.nsv", "result2283_43.nsv", "result2283_44.nsv", "result2283_45.nsv", "result2283_46.nsv", "result2283_47.nsv", "result2283_48.nsv", "result2283_49.nsv", "result2283_50.nsv", "result2283_51.nsv", "result2283_52.nsv"];
val thyn = "vfmTestDefs2283";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
