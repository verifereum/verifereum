Theory vfmTest2230[no_sig_docs]
Ancestors vfmTestDefs2230
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2230_0.nsv", "result2230_1.nsv", "result2230_2.nsv", "result2230_3.nsv", "result2230_4.nsv", "result2230_5.nsv", "result2230_6.nsv", "result2230_7.nsv", "result2230_8.nsv", "result2230_9.nsv", "result2230_10.nsv", "result2230_11.nsv", "result2230_12.nsv", "result2230_13.nsv", "result2230_14.nsv", "result2230_15.nsv", "result2230_16.nsv", "result2230_17.nsv", "result2230_18.nsv", "result2230_19.nsv", "result2230_20.nsv", "result2230_21.nsv", "result2230_22.nsv", "result2230_23.nsv", "result2230_24.nsv", "result2230_25.nsv", "result2230_26.nsv", "result2230_27.nsv", "result2230_28.nsv", "result2230_29.nsv", "result2230_30.nsv", "result2230_31.nsv", "result2230_32.nsv", "result2230_33.nsv", "result2230_34.nsv", "result2230_35.nsv", "result2230_36.nsv", "result2230_37.nsv", "result2230_38.nsv", "result2230_39.nsv", "result2230_40.nsv", "result2230_41.nsv", "result2230_42.nsv", "result2230_43.nsv", "result2230_44.nsv", "result2230_45.nsv", "result2230_46.nsv", "result2230_47.nsv", "result2230_48.nsv", "result2230_49.nsv", "result2230_50.nsv", "result2230_51.nsv", "result2230_52.nsv", "result2230_53.nsv", "result2230_54.nsv", "result2230_55.nsv", "result2230_56.nsv", "result2230_57.nsv", "result2230_58.nsv", "result2230_59.nsv"];
val thyn = "vfmTestDefs2230";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
