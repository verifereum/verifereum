Theory vfmTest1439[no_sig_docs]
Ancestors vfmTestDefs1439
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1439_0.nsv", "result1439_1.nsv", "result1439_2.nsv", "result1439_3.nsv", "result1439_4.nsv", "result1439_5.nsv", "result1439_6.nsv", "result1439_7.nsv", "result1439_8.nsv", "result1439_9.nsv", "result1439_10.nsv", "result1439_11.nsv", "result1439_12.nsv", "result1439_13.nsv", "result1439_14.nsv", "result1439_15.nsv", "result1439_16.nsv", "result1439_17.nsv", "result1439_18.nsv", "result1439_19.nsv", "result1439_20.nsv", "result1439_21.nsv", "result1439_22.nsv", "result1439_23.nsv", "result1439_24.nsv", "result1439_25.nsv", "result1439_26.nsv", "result1439_27.nsv", "result1439_28.nsv", "result1439_29.nsv"];
val thyn = "vfmTestDefs1439";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
