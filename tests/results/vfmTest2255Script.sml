Theory vfmTest2255[no_sig_docs]
Ancestors vfmTestDefs2255
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2255_0.nsv", "result2255_1.nsv", "result2255_2.nsv", "result2255_3.nsv", "result2255_4.nsv", "result2255_5.nsv", "result2255_6.nsv", "result2255_7.nsv", "result2255_8.nsv", "result2255_9.nsv", "result2255_10.nsv", "result2255_11.nsv", "result2255_12.nsv", "result2255_13.nsv", "result2255_14.nsv", "result2255_15.nsv", "result2255_16.nsv", "result2255_17.nsv", "result2255_18.nsv", "result2255_19.nsv", "result2255_20.nsv", "result2255_21.nsv", "result2255_22.nsv", "result2255_23.nsv", "result2255_24.nsv", "result2255_25.nsv", "result2255_26.nsv", "result2255_27.nsv", "result2255_28.nsv", "result2255_29.nsv", "result2255_30.nsv", "result2255_31.nsv", "result2255_32.nsv", "result2255_33.nsv", "result2255_34.nsv", "result2255_35.nsv", "result2255_36.nsv", "result2255_37.nsv", "result2255_38.nsv", "result2255_39.nsv", "result2255_40.nsv", "result2255_41.nsv", "result2255_42.nsv", "result2255_43.nsv", "result2255_44.nsv", "result2255_45.nsv", "result2255_46.nsv", "result2255_47.nsv", "result2255_48.nsv", "result2255_49.nsv", "result2255_50.nsv", "result2255_51.nsv", "result2255_52.nsv", "result2255_53.nsv"];
val thyn = "vfmTestDefs2255";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
