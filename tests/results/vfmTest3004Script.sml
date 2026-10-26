Theory vfmTest3004[no_sig_docs]
Ancestors vfmTestDefs3004
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3004_0.nsv", "result3004_1.nsv", "result3004_2.nsv", "result3004_3.nsv", "result3004_4.nsv", "result3004_5.nsv", "result3004_6.nsv", "result3004_7.nsv", "result3004_8.nsv", "result3004_9.nsv", "result3004_10.nsv", "result3004_11.nsv", "result3004_12.nsv", "result3004_13.nsv", "result3004_14.nsv", "result3004_15.nsv", "result3004_16.nsv", "result3004_17.nsv", "result3004_18.nsv"];
val thyn = "vfmTestDefs3004";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
