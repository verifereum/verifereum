Theory vfmTest2143[no_sig_docs]
Ancestors vfmTestDefs2143
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2143_0.nsv", "result2143_1.nsv", "result2143_2.nsv", "result2143_3.nsv", "result2143_4.nsv", "result2143_5.nsv", "result2143_6.nsv", "result2143_7.nsv", "result2143_8.nsv", "result2143_9.nsv", "result2143_10.nsv", "result2143_11.nsv", "result2143_12.nsv", "result2143_13.nsv", "result2143_14.nsv", "result2143_15.nsv", "result2143_16.nsv", "result2143_17.nsv", "result2143_18.nsv", "result2143_19.nsv", "result2143_20.nsv", "result2143_21.nsv", "result2143_22.nsv", "result2143_23.nsv", "result2143_24.nsv", "result2143_25.nsv", "result2143_26.nsv", "result2143_27.nsv", "result2143_28.nsv", "result2143_29.nsv", "result2143_30.nsv", "result2143_31.nsv", "result2143_32.nsv", "result2143_33.nsv", "result2143_34.nsv", "result2143_35.nsv", "result2143_36.nsv", "result2143_37.nsv", "result2143_38.nsv", "result2143_39.nsv", "result2143_40.nsv", "result2143_41.nsv", "result2143_42.nsv", "result2143_43.nsv", "result2143_44.nsv", "result2143_45.nsv", "result2143_46.nsv"];
val thyn = "vfmTestDefs2143";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
