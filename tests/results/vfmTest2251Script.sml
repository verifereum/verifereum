Theory vfmTest2251[no_sig_docs]
Ancestors vfmTestDefs2251
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2251_0.nsv", "result2251_1.nsv", "result2251_2.nsv", "result2251_3.nsv", "result2251_4.nsv", "result2251_5.nsv", "result2251_6.nsv", "result2251_7.nsv", "result2251_8.nsv", "result2251_9.nsv", "result2251_10.nsv", "result2251_11.nsv", "result2251_12.nsv", "result2251_13.nsv", "result2251_14.nsv", "result2251_15.nsv", "result2251_16.nsv", "result2251_17.nsv", "result2251_18.nsv", "result2251_19.nsv", "result2251_20.nsv", "result2251_21.nsv", "result2251_22.nsv", "result2251_23.nsv", "result2251_24.nsv", "result2251_25.nsv", "result2251_26.nsv", "result2251_27.nsv", "result2251_28.nsv", "result2251_29.nsv", "result2251_30.nsv"];
val thyn = "vfmTestDefs2251";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
