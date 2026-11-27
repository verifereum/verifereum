Theory vfmTest2150[no_sig_docs]
Ancestors vfmTestDefs2150
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2150_0.nsv", "result2150_1.nsv", "result2150_2.nsv", "result2150_3.nsv", "result2150_4.nsv", "result2150_5.nsv", "result2150_6.nsv", "result2150_7.nsv", "result2150_8.nsv", "result2150_9.nsv", "result2150_10.nsv", "result2150_11.nsv", "result2150_12.nsv", "result2150_13.nsv", "result2150_14.nsv", "result2150_15.nsv", "result2150_16.nsv", "result2150_17.nsv", "result2150_18.nsv", "result2150_19.nsv", "result2150_20.nsv", "result2150_21.nsv", "result2150_22.nsv", "result2150_23.nsv", "result2150_24.nsv", "result2150_25.nsv", "result2150_26.nsv", "result2150_27.nsv", "result2150_28.nsv", "result2150_29.nsv", "result2150_30.nsv", "result2150_31.nsv", "result2150_32.nsv", "result2150_33.nsv", "result2150_34.nsv", "result2150_35.nsv", "result2150_36.nsv", "result2150_37.nsv", "result2150_38.nsv", "result2150_39.nsv", "result2150_40.nsv", "result2150_41.nsv", "result2150_42.nsv", "result2150_43.nsv", "result2150_44.nsv", "result2150_45.nsv", "result2150_46.nsv", "result2150_47.nsv", "result2150_48.nsv", "result2150_49.nsv", "result2150_50.nsv", "result2150_51.nsv", "result2150_52.nsv", "result2150_53.nsv"];
val thyn = "vfmTestDefs2150";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
