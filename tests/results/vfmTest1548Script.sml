Theory vfmTest1548[no_sig_docs]
Ancestors vfmTestDefs1548
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1548_0.nsv", "result1548_1.nsv", "result1548_2.nsv", "result1548_3.nsv", "result1548_4.nsv", "result1548_5.nsv", "result1548_6.nsv", "result1548_7.nsv", "result1548_8.nsv", "result1548_9.nsv", "result1548_10.nsv", "result1548_11.nsv", "result1548_12.nsv", "result1548_13.nsv", "result1548_14.nsv", "result1548_15.nsv", "result1548_16.nsv", "result1548_17.nsv", "result1548_18.nsv", "result1548_19.nsv"];
val thyn = "vfmTestDefs1548";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
