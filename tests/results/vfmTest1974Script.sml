Theory vfmTest1974[no_sig_docs]
Ancestors vfmTestDefs1974
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1974_0.nsv", "result1974_1.nsv", "result1974_2.nsv", "result1974_3.nsv", "result1974_4.nsv", "result1974_5.nsv", "result1974_6.nsv", "result1974_7.nsv", "result1974_8.nsv", "result1974_9.nsv", "result1974_10.nsv", "result1974_11.nsv", "result1974_12.nsv", "result1974_13.nsv", "result1974_14.nsv", "result1974_15.nsv", "result1974_16.nsv", "result1974_17.nsv", "result1974_18.nsv", "result1974_19.nsv"];
val thyn = "vfmTestDefs1974";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
