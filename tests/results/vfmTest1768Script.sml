Theory vfmTest1768[no_sig_docs]
Ancestors vfmTestDefs1768
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1768_0.nsv", "result1768_1.nsv", "result1768_2.nsv", "result1768_3.nsv", "result1768_4.nsv", "result1768_5.nsv", "result1768_6.nsv", "result1768_7.nsv", "result1768_8.nsv", "result1768_9.nsv", "result1768_10.nsv", "result1768_11.nsv", "result1768_12.nsv", "result1768_13.nsv", "result1768_14.nsv", "result1768_15.nsv"];
val thyn = "vfmTestDefs1768";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
