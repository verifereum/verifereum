Theory vfmTest2353[no_sig_docs]
Ancestors vfmTestDefs2353
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2353_0.nsv", "result2353_1.nsv", "result2353_2.nsv", "result2353_3.nsv", "result2353_4.nsv", "result2353_5.nsv", "result2353_6.nsv", "result2353_7.nsv", "result2353_8.nsv", "result2353_9.nsv", "result2353_10.nsv", "result2353_11.nsv", "result2353_12.nsv", "result2353_13.nsv", "result2353_14.nsv", "result2353_15.nsv", "result2353_16.nsv", "result2353_17.nsv", "result2353_18.nsv", "result2353_19.nsv", "result2353_20.nsv", "result2353_21.nsv", "result2353_22.nsv", "result2353_23.nsv", "result2353_24.nsv", "result2353_25.nsv", "result2353_26.nsv", "result2353_27.nsv", "result2353_28.nsv", "result2353_29.nsv", "result2353_30.nsv", "result2353_31.nsv", "result2353_32.nsv", "result2353_33.nsv", "result2353_34.nsv", "result2353_35.nsv", "result2353_36.nsv", "result2353_37.nsv", "result2353_38.nsv", "result2353_39.nsv", "result2353_40.nsv", "result2353_41.nsv", "result2353_42.nsv", "result2353_43.nsv", "result2353_44.nsv", "result2353_45.nsv", "result2353_46.nsv", "result2353_47.nsv"];
val thyn = "vfmTestDefs2353";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
