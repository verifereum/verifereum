Theory vfmTest1565[no_sig_docs]
Ancestors vfmTestDefs1565
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1565_0.nsv", "result1565_1.nsv", "result1565_2.nsv", "result1565_3.nsv", "result1565_4.nsv", "result1565_5.nsv", "result1565_6.nsv", "result1565_7.nsv", "result1565_8.nsv", "result1565_9.nsv", "result1565_10.nsv", "result1565_11.nsv", "result1565_12.nsv", "result1565_13.nsv", "result1565_14.nsv", "result1565_15.nsv", "result1565_16.nsv", "result1565_17.nsv", "result1565_18.nsv", "result1565_19.nsv"];
val thyn = "vfmTestDefs1565";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
