Theory vfmTest2331[no_sig_docs]
Ancestors vfmTestDefs2331
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2331_0.nsv", "result2331_1.nsv", "result2331_2.nsv", "result2331_3.nsv", "result2331_4.nsv", "result2331_5.nsv", "result2331_6.nsv", "result2331_7.nsv", "result2331_8.nsv", "result2331_9.nsv", "result2331_10.nsv", "result2331_11.nsv", "result2331_12.nsv", "result2331_13.nsv", "result2331_14.nsv", "result2331_15.nsv", "result2331_16.nsv", "result2331_17.nsv", "result2331_18.nsv", "result2331_19.nsv", "result2331_20.nsv", "result2331_21.nsv", "result2331_22.nsv", "result2331_23.nsv", "result2331_24.nsv", "result2331_25.nsv", "result2331_26.nsv", "result2331_27.nsv", "result2331_28.nsv", "result2331_29.nsv", "result2331_30.nsv", "result2331_31.nsv", "result2331_32.nsv", "result2331_33.nsv", "result2331_34.nsv", "result2331_35.nsv", "result2331_36.nsv", "result2331_37.nsv", "result2331_38.nsv", "result2331_39.nsv", "result2331_40.nsv", "result2331_41.nsv", "result2331_42.nsv", "result2331_43.nsv", "result2331_44.nsv", "result2331_45.nsv", "result2331_46.nsv", "result2331_47.nsv"];
val thyn = "vfmTestDefs2331";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
