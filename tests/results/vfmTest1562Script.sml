Theory vfmTest1562[no_sig_docs]
Ancestors vfmTestDefs1562
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1562_0.nsv", "result1562_1.nsv", "result1562_2.nsv", "result1562_3.nsv", "result1562_4.nsv", "result1562_5.nsv", "result1562_6.nsv", "result1562_7.nsv", "result1562_8.nsv", "result1562_9.nsv", "result1562_10.nsv", "result1562_11.nsv", "result1562_12.nsv", "result1562_13.nsv", "result1562_14.nsv", "result1562_15.nsv", "result1562_16.nsv", "result1562_17.nsv", "result1562_18.nsv", "result1562_19.nsv"];
val thyn = "vfmTestDefs1562";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
