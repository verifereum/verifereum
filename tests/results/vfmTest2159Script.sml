Theory vfmTest2159[no_sig_docs]
Ancestors vfmTestDefs2159
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2159_0.nsv", "result2159_1.nsv", "result2159_2.nsv", "result2159_3.nsv", "result2159_4.nsv", "result2159_5.nsv", "result2159_6.nsv", "result2159_7.nsv", "result2159_8.nsv", "result2159_9.nsv", "result2159_10.nsv", "result2159_11.nsv", "result2159_12.nsv", "result2159_13.nsv", "result2159_14.nsv", "result2159_15.nsv", "result2159_16.nsv", "result2159_17.nsv", "result2159_18.nsv", "result2159_19.nsv", "result2159_20.nsv", "result2159_21.nsv", "result2159_22.nsv", "result2159_23.nsv", "result2159_24.nsv", "result2159_25.nsv", "result2159_26.nsv", "result2159_27.nsv", "result2159_28.nsv", "result2159_29.nsv", "result2159_30.nsv", "result2159_31.nsv", "result2159_32.nsv", "result2159_33.nsv", "result2159_34.nsv", "result2159_35.nsv", "result2159_36.nsv", "result2159_37.nsv", "result2159_38.nsv", "result2159_39.nsv", "result2159_40.nsv", "result2159_41.nsv", "result2159_42.nsv", "result2159_43.nsv", "result2159_44.nsv", "result2159_45.nsv", "result2159_46.nsv", "result2159_47.nsv", "result2159_48.nsv", "result2159_49.nsv", "result2159_50.nsv", "result2159_51.nsv", "result2159_52.nsv", "result2159_53.nsv", "result2159_54.nsv", "result2159_55.nsv"];
val thyn = "vfmTestDefs2159";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
