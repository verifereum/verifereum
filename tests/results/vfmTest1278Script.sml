Theory vfmTest1278[no_sig_docs]
Ancestors vfmTestDefs1278
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1278_0.nsv", "result1278_1.nsv", "result1278_2.nsv", "result1278_3.nsv", "result1278_4.nsv", "result1278_5.nsv", "result1278_6.nsv", "result1278_7.nsv", "result1278_8.nsv", "result1278_9.nsv", "result1278_10.nsv", "result1278_11.nsv", "result1278_12.nsv", "result1278_13.nsv", "result1278_14.nsv", "result1278_15.nsv", "result1278_16.nsv", "result1278_17.nsv", "result1278_18.nsv", "result1278_19.nsv", "result1278_20.nsv", "result1278_21.nsv", "result1278_22.nsv", "result1278_23.nsv", "result1278_24.nsv", "result1278_25.nsv", "result1278_26.nsv"];
val thyn = "vfmTestDefs1278";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
