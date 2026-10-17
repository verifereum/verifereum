Theory vfmTest1752[no_sig_docs]
Ancestors vfmTestDefs1752
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1752_0.nsv", "result1752_1.nsv", "result1752_2.nsv", "result1752_3.nsv", "result1752_4.nsv", "result1752_5.nsv", "result1752_6.nsv", "result1752_7.nsv", "result1752_8.nsv", "result1752_9.nsv", "result1752_10.nsv", "result1752_11.nsv", "result1752_12.nsv", "result1752_13.nsv", "result1752_14.nsv", "result1752_15.nsv"];
val thyn = "vfmTestDefs1752";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
