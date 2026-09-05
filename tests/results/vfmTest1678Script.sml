Theory vfmTest1678[no_sig_docs]
Ancestors vfmTestDefs1678
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1678_0.nsv", "result1678_1.nsv", "result1678_2.nsv", "result1678_3.nsv", "result1678_4.nsv", "result1678_5.nsv", "result1678_6.nsv", "result1678_7.nsv", "result1678_8.nsv", "result1678_9.nsv", "result1678_10.nsv", "result1678_11.nsv", "result1678_12.nsv", "result1678_13.nsv", "result1678_14.nsv", "result1678_15.nsv"];
val thyn = "vfmTestDefs1678";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
