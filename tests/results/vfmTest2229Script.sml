Theory vfmTest2229[no_sig_docs]
Ancestors vfmTestDefs2229
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2229_0.nsv", "result2229_1.nsv", "result2229_2.nsv", "result2229_3.nsv", "result2229_4.nsv", "result2229_5.nsv", "result2229_6.nsv", "result2229_7.nsv", "result2229_8.nsv", "result2229_9.nsv", "result2229_10.nsv", "result2229_11.nsv", "result2229_12.nsv", "result2229_13.nsv", "result2229_14.nsv", "result2229_15.nsv", "result2229_16.nsv", "result2229_17.nsv", "result2229_18.nsv", "result2229_19.nsv", "result2229_20.nsv", "result2229_21.nsv", "result2229_22.nsv", "result2229_23.nsv", "result2229_24.nsv", "result2229_25.nsv", "result2229_26.nsv", "result2229_27.nsv", "result2229_28.nsv", "result2229_29.nsv", "result2229_30.nsv", "result2229_31.nsv", "result2229_32.nsv", "result2229_33.nsv", "result2229_34.nsv", "result2229_35.nsv", "result2229_36.nsv", "result2229_37.nsv", "result2229_38.nsv", "result2229_39.nsv", "result2229_40.nsv", "result2229_41.nsv", "result2229_42.nsv", "result2229_43.nsv", "result2229_44.nsv", "result2229_45.nsv", "result2229_46.nsv", "result2229_47.nsv"];
val thyn = "vfmTestDefs2229";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
