Theory vfmTest1538[no_sig_docs]
Ancestors vfmTestDefs1538
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1538_0.nsv", "result1538_1.nsv", "result1538_2.nsv", "result1538_3.nsv", "result1538_4.nsv", "result1538_5.nsv", "result1538_6.nsv", "result1538_7.nsv", "result1538_8.nsv", "result1538_9.nsv", "result1538_10.nsv", "result1538_11.nsv", "result1538_12.nsv", "result1538_13.nsv", "result1538_14.nsv", "result1538_15.nsv", "result1538_16.nsv", "result1538_17.nsv", "result1538_18.nsv", "result1538_19.nsv"];
val thyn = "vfmTestDefs1538";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
