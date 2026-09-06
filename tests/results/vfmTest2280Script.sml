Theory vfmTest2280[no_sig_docs]
Ancestors vfmTestDefs2280
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2280_0.nsv", "result2280_1.nsv", "result2280_2.nsv", "result2280_3.nsv", "result2280_4.nsv", "result2280_5.nsv", "result2280_6.nsv", "result2280_7.nsv", "result2280_8.nsv", "result2280_9.nsv", "result2280_10.nsv", "result2280_11.nsv", "result2280_12.nsv", "result2280_13.nsv", "result2280_14.nsv", "result2280_15.nsv", "result2280_16.nsv", "result2280_17.nsv", "result2280_18.nsv", "result2280_19.nsv", "result2280_20.nsv", "result2280_21.nsv", "result2280_22.nsv", "result2280_23.nsv", "result2280_24.nsv", "result2280_25.nsv", "result2280_26.nsv"];
val thyn = "vfmTestDefs2280";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
