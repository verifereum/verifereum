Theory vfmTest2354[no_sig_docs]
Ancestors vfmTestDefs2354
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2354_0.nsv", "result2354_1.nsv", "result2354_2.nsv", "result2354_3.nsv", "result2354_4.nsv", "result2354_5.nsv", "result2354_6.nsv", "result2354_7.nsv", "result2354_8.nsv", "result2354_9.nsv", "result2354_10.nsv", "result2354_11.nsv", "result2354_12.nsv", "result2354_13.nsv", "result2354_14.nsv", "result2354_15.nsv", "result2354_16.nsv", "result2354_17.nsv", "result2354_18.nsv", "result2354_19.nsv", "result2354_20.nsv", "result2354_21.nsv", "result2354_22.nsv", "result2354_23.nsv", "result2354_24.nsv", "result2354_25.nsv", "result2354_26.nsv", "result2354_27.nsv", "result2354_28.nsv", "result2354_29.nsv", "result2354_30.nsv", "result2354_31.nsv", "result2354_32.nsv", "result2354_33.nsv", "result2354_34.nsv", "result2354_35.nsv", "result2354_36.nsv", "result2354_37.nsv", "result2354_38.nsv", "result2354_39.nsv", "result2354_40.nsv", "result2354_41.nsv", "result2354_42.nsv", "result2354_43.nsv", "result2354_44.nsv", "result2354_45.nsv", "result2354_46.nsv", "result2354_47.nsv", "result2354_48.nsv", "result2354_49.nsv", "result2354_50.nsv", "result2354_51.nsv", "result2354_52.nsv", "result2354_53.nsv", "result2354_54.nsv", "result2354_55.nsv", "result2354_56.nsv", "result2354_57.nsv", "result2354_58.nsv", "result2354_59.nsv"];
val thyn = "vfmTestDefs2354";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
