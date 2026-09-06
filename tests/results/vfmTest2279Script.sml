Theory vfmTest2279[no_sig_docs]
Ancestors vfmTestDefs2279
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2279_0.nsv", "result2279_1.nsv", "result2279_2.nsv", "result2279_3.nsv", "result2279_4.nsv", "result2279_5.nsv", "result2279_6.nsv", "result2279_7.nsv", "result2279_8.nsv", "result2279_9.nsv", "result2279_10.nsv", "result2279_11.nsv", "result2279_12.nsv", "result2279_13.nsv", "result2279_14.nsv", "result2279_15.nsv", "result2279_16.nsv", "result2279_17.nsv", "result2279_18.nsv", "result2279_19.nsv", "result2279_20.nsv", "result2279_21.nsv", "result2279_22.nsv", "result2279_23.nsv", "result2279_24.nsv", "result2279_25.nsv", "result2279_26.nsv", "result2279_27.nsv", "result2279_28.nsv", "result2279_29.nsv", "result2279_30.nsv", "result2279_31.nsv", "result2279_32.nsv", "result2279_33.nsv", "result2279_34.nsv", "result2279_35.nsv", "result2279_36.nsv", "result2279_37.nsv", "result2279_38.nsv", "result2279_39.nsv", "result2279_40.nsv", "result2279_41.nsv", "result2279_42.nsv", "result2279_43.nsv", "result2279_44.nsv", "result2279_45.nsv", "result2279_46.nsv", "result2279_47.nsv", "result2279_48.nsv", "result2279_49.nsv", "result2279_50.nsv", "result2279_51.nsv", "result2279_52.nsv", "result2279_53.nsv"];
val thyn = "vfmTestDefs2279";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
