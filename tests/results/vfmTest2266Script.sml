Theory vfmTest2266[no_sig_docs]
Ancestors vfmTestDefs2266
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2266_0.nsv", "result2266_1.nsv", "result2266_2.nsv", "result2266_3.nsv", "result2266_4.nsv", "result2266_5.nsv", "result2266_6.nsv", "result2266_7.nsv", "result2266_8.nsv", "result2266_9.nsv", "result2266_10.nsv", "result2266_11.nsv", "result2266_12.nsv", "result2266_13.nsv", "result2266_14.nsv", "result2266_15.nsv", "result2266_16.nsv", "result2266_17.nsv", "result2266_18.nsv", "result2266_19.nsv", "result2266_20.nsv", "result2266_21.nsv", "result2266_22.nsv", "result2266_23.nsv", "result2266_24.nsv", "result2266_25.nsv", "result2266_26.nsv", "result2266_27.nsv", "result2266_28.nsv", "result2266_29.nsv", "result2266_30.nsv", "result2266_31.nsv", "result2266_32.nsv", "result2266_33.nsv", "result2266_34.nsv", "result2266_35.nsv", "result2266_36.nsv", "result2266_37.nsv", "result2266_38.nsv", "result2266_39.nsv", "result2266_40.nsv", "result2266_41.nsv", "result2266_42.nsv", "result2266_43.nsv", "result2266_44.nsv", "result2266_45.nsv", "result2266_46.nsv", "result2266_47.nsv", "result2266_48.nsv", "result2266_49.nsv", "result2266_50.nsv", "result2266_51.nsv", "result2266_52.nsv", "result2266_53.nsv", "result2266_54.nsv"];
val thyn = "vfmTestDefs2266";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
