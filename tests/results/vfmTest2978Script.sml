Theory vfmTest2978[no_sig_docs]
Ancestors vfmTestDefs2978
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2978_0.nsv", "result2978_1.nsv", "result2978_2.nsv", "result2978_3.nsv", "result2978_4.nsv", "result2978_5.nsv", "result2978_6.nsv", "result2978_7.nsv", "result2978_8.nsv", "result2978_9.nsv", "result2978_10.nsv", "result2978_11.nsv", "result2978_12.nsv", "result2978_13.nsv", "result2978_14.nsv", "result2978_15.nsv", "result2978_16.nsv", "result2978_17.nsv", "result2978_18.nsv", "result2978_19.nsv", "result2978_20.nsv", "result2978_21.nsv", "result2978_22.nsv", "result2978_23.nsv", "result2978_24.nsv", "result2978_25.nsv", "result2978_26.nsv", "result2978_27.nsv", "result2978_28.nsv", "result2978_29.nsv", "result2978_30.nsv", "result2978_31.nsv", "result2978_32.nsv", "result2978_33.nsv", "result2978_34.nsv", "result2978_35.nsv", "result2978_36.nsv", "result2978_37.nsv", "result2978_38.nsv", "result2978_39.nsv", "result2978_40.nsv", "result2978_41.nsv", "result2978_42.nsv", "result2978_43.nsv", "result2978_44.nsv", "result2978_45.nsv", "result2978_46.nsv"];
val thyn = "vfmTestDefs2978";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
