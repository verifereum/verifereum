Theory vfmTest2128[no_sig_docs]
Ancestors vfmTestDefs2128
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2128_0.nsv", "result2128_1.nsv", "result2128_2.nsv", "result2128_3.nsv", "result2128_4.nsv", "result2128_5.nsv", "result2128_6.nsv", "result2128_7.nsv", "result2128_8.nsv", "result2128_9.nsv", "result2128_10.nsv", "result2128_11.nsv", "result2128_12.nsv", "result2128_13.nsv", "result2128_14.nsv", "result2128_15.nsv", "result2128_16.nsv", "result2128_17.nsv", "result2128_18.nsv", "result2128_19.nsv", "result2128_20.nsv", "result2128_21.nsv", "result2128_22.nsv", "result2128_23.nsv", "result2128_24.nsv", "result2128_25.nsv", "result2128_26.nsv", "result2128_27.nsv", "result2128_28.nsv", "result2128_29.nsv", "result2128_30.nsv", "result2128_31.nsv", "result2128_32.nsv", "result2128_33.nsv", "result2128_34.nsv", "result2128_35.nsv", "result2128_36.nsv", "result2128_37.nsv", "result2128_38.nsv", "result2128_39.nsv", "result2128_40.nsv", "result2128_41.nsv", "result2128_42.nsv", "result2128_43.nsv", "result2128_44.nsv", "result2128_45.nsv", "result2128_46.nsv"];
val thyn = "vfmTestDefs2128";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
