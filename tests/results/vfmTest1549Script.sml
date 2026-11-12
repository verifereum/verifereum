Theory vfmTest1549[no_sig_docs]
Ancestors vfmTestDefs1549
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1549_0.nsv", "result1549_1.nsv", "result1549_2.nsv", "result1549_3.nsv", "result1549_4.nsv", "result1549_5.nsv", "result1549_6.nsv", "result1549_7.nsv", "result1549_8.nsv", "result1549_9.nsv", "result1549_10.nsv", "result1549_11.nsv", "result1549_12.nsv", "result1549_13.nsv", "result1549_14.nsv", "result1549_15.nsv", "result1549_16.nsv", "result1549_17.nsv", "result1549_18.nsv", "result1549_19.nsv"];
val thyn = "vfmTestDefs1549";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
