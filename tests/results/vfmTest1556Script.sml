Theory vfmTest1556[no_sig_docs]
Ancestors vfmTestDefs1556
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1556_0.nsv", "result1556_1.nsv", "result1556_2.nsv", "result1556_3.nsv", "result1556_4.nsv", "result1556_5.nsv", "result1556_6.nsv", "result1556_7.nsv", "result1556_8.nsv", "result1556_9.nsv", "result1556_10.nsv", "result1556_11.nsv", "result1556_12.nsv", "result1556_13.nsv", "result1556_14.nsv", "result1556_15.nsv", "result1556_16.nsv", "result1556_17.nsv", "result1556_18.nsv", "result1556_19.nsv"];
val thyn = "vfmTestDefs1556";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
