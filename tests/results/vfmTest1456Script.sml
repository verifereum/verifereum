Theory vfmTest1456[no_sig_docs]
Ancestors vfmTestDefs1456
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1456_0.nsv", "result1456_1.nsv", "result1456_2.nsv", "result1456_3.nsv", "result1456_4.nsv", "result1456_5.nsv", "result1456_6.nsv", "result1456_7.nsv", "result1456_8.nsv", "result1456_9.nsv", "result1456_10.nsv", "result1456_11.nsv", "result1456_12.nsv", "result1456_13.nsv", "result1456_14.nsv", "result1456_15.nsv", "result1456_16.nsv", "result1456_17.nsv", "result1456_18.nsv", "result1456_19.nsv", "result1456_20.nsv", "result1456_21.nsv", "result1456_22.nsv", "result1456_23.nsv", "result1456_24.nsv", "result1456_25.nsv", "result1456_26.nsv", "result1456_27.nsv", "result1456_28.nsv", "result1456_29.nsv", "result1456_30.nsv", "result1456_31.nsv", "result1456_32.nsv", "result1456_33.nsv", "result1456_34.nsv", "result1456_35.nsv", "result1456_36.nsv", "result1456_37.nsv", "result1456_38.nsv", "result1456_39.nsv", "result1456_40.nsv", "result1456_41.nsv", "result1456_42.nsv", "result1456_43.nsv", "result1456_44.nsv", "result1456_45.nsv", "result1456_46.nsv", "result1456_47.nsv", "result1456_48.nsv", "result1456_49.nsv", "result1456_50.nsv", "result1456_51.nsv", "result1456_52.nsv", "result1456_53.nsv", "result1456_54.nsv"];
val thyn = "vfmTestDefs1456";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
