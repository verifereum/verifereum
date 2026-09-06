Theory vfmTest2272[no_sig_docs]
Ancestors vfmTestDefs2272
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2272_0.nsv", "result2272_1.nsv", "result2272_2.nsv", "result2272_3.nsv", "result2272_4.nsv", "result2272_5.nsv", "result2272_6.nsv", "result2272_7.nsv", "result2272_8.nsv", "result2272_9.nsv", "result2272_10.nsv", "result2272_11.nsv", "result2272_12.nsv", "result2272_13.nsv", "result2272_14.nsv", "result2272_15.nsv", "result2272_16.nsv", "result2272_17.nsv", "result2272_18.nsv", "result2272_19.nsv", "result2272_20.nsv", "result2272_21.nsv", "result2272_22.nsv", "result2272_23.nsv", "result2272_24.nsv", "result2272_25.nsv", "result2272_26.nsv", "result2272_27.nsv", "result2272_28.nsv", "result2272_29.nsv", "result2272_30.nsv", "result2272_31.nsv", "result2272_32.nsv", "result2272_33.nsv", "result2272_34.nsv", "result2272_35.nsv", "result2272_36.nsv", "result2272_37.nsv", "result2272_38.nsv", "result2272_39.nsv", "result2272_40.nsv", "result2272_41.nsv", "result2272_42.nsv", "result2272_43.nsv", "result2272_44.nsv", "result2272_45.nsv", "result2272_46.nsv"];
val thyn = "vfmTestDefs2272";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
