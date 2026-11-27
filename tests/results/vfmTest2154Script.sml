Theory vfmTest2154[no_sig_docs]
Ancestors vfmTestDefs2154
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2154_0.nsv", "result2154_1.nsv", "result2154_2.nsv", "result2154_3.nsv", "result2154_4.nsv", "result2154_5.nsv", "result2154_6.nsv", "result2154_7.nsv", "result2154_8.nsv", "result2154_9.nsv", "result2154_10.nsv", "result2154_11.nsv", "result2154_12.nsv", "result2154_13.nsv", "result2154_14.nsv", "result2154_15.nsv", "result2154_16.nsv", "result2154_17.nsv", "result2154_18.nsv", "result2154_19.nsv", "result2154_20.nsv", "result2154_21.nsv", "result2154_22.nsv", "result2154_23.nsv", "result2154_24.nsv", "result2154_25.nsv", "result2154_26.nsv", "result2154_27.nsv", "result2154_28.nsv", "result2154_29.nsv", "result2154_30.nsv", "result2154_31.nsv", "result2154_32.nsv", "result2154_33.nsv", "result2154_34.nsv", "result2154_35.nsv", "result2154_36.nsv", "result2154_37.nsv", "result2154_38.nsv", "result2154_39.nsv", "result2154_40.nsv", "result2154_41.nsv", "result2154_42.nsv", "result2154_43.nsv", "result2154_44.nsv", "result2154_45.nsv", "result2154_46.nsv", "result2154_47.nsv", "result2154_48.nsv", "result2154_49.nsv", "result2154_50.nsv", "result2154_51.nsv", "result2154_52.nsv"];
val thyn = "vfmTestDefs2154";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
