Theory vfmTest2310[no_sig_docs]
Ancestors vfmTestDefs2310
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2310_0.nsv", "result2310_1.nsv", "result2310_2.nsv", "result2310_3.nsv", "result2310_4.nsv", "result2310_5.nsv", "result2310_6.nsv", "result2310_7.nsv", "result2310_8.nsv", "result2310_9.nsv", "result2310_10.nsv", "result2310_11.nsv", "result2310_12.nsv", "result2310_13.nsv", "result2310_14.nsv", "result2310_15.nsv", "result2310_16.nsv", "result2310_17.nsv", "result2310_18.nsv", "result2310_19.nsv", "result2310_20.nsv", "result2310_21.nsv", "result2310_22.nsv", "result2310_23.nsv", "result2310_24.nsv", "result2310_25.nsv", "result2310_26.nsv", "result2310_27.nsv", "result2310_28.nsv", "result2310_29.nsv", "result2310_30.nsv", "result2310_31.nsv", "result2310_32.nsv", "result2310_33.nsv", "result2310_34.nsv", "result2310_35.nsv", "result2310_36.nsv", "result2310_37.nsv", "result2310_38.nsv", "result2310_39.nsv"];
val thyn = "vfmTestDefs2310";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
