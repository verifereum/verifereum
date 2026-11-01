Theory vfmTest1280[no_sig_docs]
Ancestors vfmTestDefs1280
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1280_0.nsv", "result1280_1.nsv", "result1280_2.nsv", "result1280_3.nsv", "result1280_4.nsv", "result1280_5.nsv", "result1280_6.nsv", "result1280_7.nsv", "result1280_8.nsv", "result1280_9.nsv", "result1280_10.nsv", "result1280_11.nsv", "result1280_12.nsv", "result1280_13.nsv", "result1280_14.nsv", "result1280_15.nsv", "result1280_16.nsv", "result1280_17.nsv", "result1280_18.nsv", "result1280_19.nsv", "result1280_20.nsv", "result1280_21.nsv", "result1280_22.nsv", "result1280_23.nsv", "result1280_24.nsv", "result1280_25.nsv", "result1280_26.nsv"];
val thyn = "vfmTestDefs1280";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
