Theory vfmTest3135[no_sig_docs]
Ancestors vfmTestDefs3135
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3135_0.nsv", "result3135_1.nsv", "result3135_2.nsv", "result3135_3.nsv", "result3135_4.nsv", "result3135_5.nsv", "result3135_6.nsv", "result3135_7.nsv", "result3135_8.nsv", "result3135_9.nsv", "result3135_10.nsv", "result3135_11.nsv", "result3135_12.nsv", "result3135_13.nsv", "result3135_14.nsv", "result3135_15.nsv", "result3135_16.nsv", "result3135_17.nsv", "result3135_18.nsv", "result3135_19.nsv", "result3135_20.nsv", "result3135_21.nsv", "result3135_22.nsv", "result3135_23.nsv", "result3135_24.nsv", "result3135_25.nsv", "result3135_26.nsv", "result3135_27.nsv", "result3135_28.nsv", "result3135_29.nsv", "result3135_30.nsv", "result3135_31.nsv"];
val thyn = "vfmTestDefs3135";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
