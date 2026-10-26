Theory vfmTest1003[no_sig_docs]
Ancestors vfmTestDefs1003
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1003_0.nsv", "result1003_1.nsv", "result1003_2.nsv", "result1003_3.nsv", "result1003_4.nsv", "result1003_5.nsv", "result1003_6.nsv", "result1003_7.nsv", "result1003_8.nsv", "result1003_9.nsv", "result1003_10.nsv", "result1003_11.nsv", "result1003_12.nsv", "result1003_13.nsv", "result1003_14.nsv", "result1003_15.nsv", "result1003_16.nsv", "result1003_17.nsv"];
val thyn = "vfmTestDefs1003";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
