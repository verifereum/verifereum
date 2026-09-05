Theory vfmTest2290[no_sig_docs]
Ancestors vfmTestDefs2290
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2290_0.nsv", "result2290_1.nsv", "result2290_2.nsv", "result2290_3.nsv", "result2290_4.nsv", "result2290_5.nsv", "result2290_6.nsv", "result2290_7.nsv", "result2290_8.nsv", "result2290_9.nsv", "result2290_10.nsv", "result2290_11.nsv", "result2290_12.nsv", "result2290_13.nsv", "result2290_14.nsv", "result2290_15.nsv", "result2290_16.nsv", "result2290_17.nsv", "result2290_18.nsv", "result2290_19.nsv", "result2290_20.nsv", "result2290_21.nsv", "result2290_22.nsv", "result2290_23.nsv", "result2290_24.nsv", "result2290_25.nsv", "result2290_26.nsv", "result2290_27.nsv", "result2290_28.nsv", "result2290_29.nsv", "result2290_30.nsv", "result2290_31.nsv", "result2290_32.nsv", "result2290_33.nsv", "result2290_34.nsv", "result2290_35.nsv", "result2290_36.nsv", "result2290_37.nsv", "result2290_38.nsv", "result2290_39.nsv", "result2290_40.nsv", "result2290_41.nsv", "result2290_42.nsv", "result2290_43.nsv", "result2290_44.nsv", "result2290_45.nsv", "result2290_46.nsv", "result2290_47.nsv", "result2290_48.nsv", "result2290_49.nsv", "result2290_50.nsv", "result2290_51.nsv", "result2290_52.nsv", "result2290_53.nsv", "result2290_54.nsv"];
val thyn = "vfmTestDefs2290";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
