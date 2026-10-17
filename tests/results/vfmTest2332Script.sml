Theory vfmTest2332[no_sig_docs]
Ancestors vfmTestDefs2332
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2332_0.nsv", "result2332_1.nsv", "result2332_2.nsv", "result2332_3.nsv", "result2332_4.nsv", "result2332_5.nsv", "result2332_6.nsv", "result2332_7.nsv", "result2332_8.nsv", "result2332_9.nsv", "result2332_10.nsv", "result2332_11.nsv", "result2332_12.nsv", "result2332_13.nsv", "result2332_14.nsv", "result2332_15.nsv", "result2332_16.nsv", "result2332_17.nsv", "result2332_18.nsv", "result2332_19.nsv", "result2332_20.nsv", "result2332_21.nsv", "result2332_22.nsv", "result2332_23.nsv", "result2332_24.nsv", "result2332_25.nsv", "result2332_26.nsv", "result2332_27.nsv", "result2332_28.nsv", "result2332_29.nsv", "result2332_30.nsv", "result2332_31.nsv", "result2332_32.nsv", "result2332_33.nsv", "result2332_34.nsv", "result2332_35.nsv", "result2332_36.nsv", "result2332_37.nsv", "result2332_38.nsv", "result2332_39.nsv", "result2332_40.nsv", "result2332_41.nsv", "result2332_42.nsv", "result2332_43.nsv", "result2332_44.nsv", "result2332_45.nsv", "result2332_46.nsv", "result2332_47.nsv", "result2332_48.nsv", "result2332_49.nsv", "result2332_50.nsv", "result2332_51.nsv", "result2332_52.nsv", "result2332_53.nsv", "result2332_54.nsv", "result2332_55.nsv", "result2332_56.nsv", "result2332_57.nsv", "result2332_58.nsv", "result2332_59.nsv"];
val thyn = "vfmTestDefs2332";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
