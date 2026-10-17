Theory vfmTest2259[no_sig_docs]
Ancestors vfmTestDefs2259
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2259_0.nsv", "result2259_1.nsv", "result2259_2.nsv", "result2259_3.nsv", "result2259_4.nsv", "result2259_5.nsv", "result2259_6.nsv", "result2259_7.nsv", "result2259_8.nsv", "result2259_9.nsv", "result2259_10.nsv", "result2259_11.nsv", "result2259_12.nsv", "result2259_13.nsv", "result2259_14.nsv", "result2259_15.nsv", "result2259_16.nsv", "result2259_17.nsv", "result2259_18.nsv", "result2259_19.nsv", "result2259_20.nsv", "result2259_21.nsv", "result2259_22.nsv", "result2259_23.nsv", "result2259_24.nsv", "result2259_25.nsv", "result2259_26.nsv", "result2259_27.nsv", "result2259_28.nsv", "result2259_29.nsv", "result2259_30.nsv", "result2259_31.nsv", "result2259_32.nsv", "result2259_33.nsv", "result2259_34.nsv", "result2259_35.nsv", "result2259_36.nsv", "result2259_37.nsv", "result2259_38.nsv", "result2259_39.nsv", "result2259_40.nsv", "result2259_41.nsv", "result2259_42.nsv", "result2259_43.nsv", "result2259_44.nsv", "result2259_45.nsv", "result2259_46.nsv", "result2259_47.nsv", "result2259_48.nsv", "result2259_49.nsv", "result2259_50.nsv", "result2259_51.nsv", "result2259_52.nsv"];
val thyn = "vfmTestDefs2259";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
