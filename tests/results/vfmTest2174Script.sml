Theory vfmTest2174[no_sig_docs]
Ancestors vfmTestDefs2174
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2174_0.nsv", "result2174_1.nsv", "result2174_2.nsv", "result2174_3.nsv", "result2174_4.nsv", "result2174_5.nsv", "result2174_6.nsv", "result2174_7.nsv", "result2174_8.nsv", "result2174_9.nsv", "result2174_10.nsv", "result2174_11.nsv", "result2174_12.nsv", "result2174_13.nsv", "result2174_14.nsv", "result2174_15.nsv", "result2174_16.nsv", "result2174_17.nsv", "result2174_18.nsv", "result2174_19.nsv", "result2174_20.nsv", "result2174_21.nsv", "result2174_22.nsv", "result2174_23.nsv", "result2174_24.nsv", "result2174_25.nsv", "result2174_26.nsv", "result2174_27.nsv", "result2174_28.nsv", "result2174_29.nsv", "result2174_30.nsv", "result2174_31.nsv", "result2174_32.nsv", "result2174_33.nsv", "result2174_34.nsv", "result2174_35.nsv", "result2174_36.nsv", "result2174_37.nsv", "result2174_38.nsv", "result2174_39.nsv", "result2174_40.nsv", "result2174_41.nsv", "result2174_42.nsv", "result2174_43.nsv", "result2174_44.nsv", "result2174_45.nsv", "result2174_46.nsv", "result2174_47.nsv", "result2174_48.nsv", "result2174_49.nsv", "result2174_50.nsv", "result2174_51.nsv", "result2174_52.nsv", "result2174_53.nsv", "result2174_54.nsv", "result2174_55.nsv"];
val thyn = "vfmTestDefs2174";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
