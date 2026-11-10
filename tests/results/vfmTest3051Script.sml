Theory vfmTest3051[no_sig_docs]
Ancestors vfmTestDefs3051
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3051_0.nsv", "result3051_1.nsv", "result3051_2.nsv", "result3051_3.nsv", "result3051_4.nsv", "result3051_5.nsv", "result3051_6.nsv", "result3051_7.nsv", "result3051_8.nsv", "result3051_9.nsv", "result3051_10.nsv", "result3051_11.nsv", "result3051_12.nsv", "result3051_13.nsv", "result3051_14.nsv", "result3051_15.nsv", "result3051_16.nsv", "result3051_17.nsv", "result3051_18.nsv", "result3051_19.nsv", "result3051_20.nsv", "result3051_21.nsv", "result3051_22.nsv", "result3051_23.nsv", "result3051_24.nsv", "result3051_25.nsv", "result3051_26.nsv", "result3051_27.nsv", "result3051_28.nsv", "result3051_29.nsv"];
val thyn = "vfmTestDefs3051";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
