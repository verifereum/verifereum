Theory vfmTest1535[no_sig_docs]
Ancestors vfmTestDefs1535
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1535_0.nsv", "result1535_1.nsv", "result1535_2.nsv", "result1535_3.nsv", "result1535_4.nsv", "result1535_5.nsv", "result1535_6.nsv", "result1535_7.nsv", "result1535_8.nsv", "result1535_9.nsv", "result1535_10.nsv", "result1535_11.nsv", "result1535_12.nsv", "result1535_13.nsv", "result1535_14.nsv", "result1535_15.nsv", "result1535_16.nsv", "result1535_17.nsv", "result1535_18.nsv", "result1535_19.nsv"];
val thyn = "vfmTestDefs1535";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
