Theory vfmTest1552[no_sig_docs]
Ancestors vfmTestDefs1552
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1552_0.nsv", "result1552_1.nsv", "result1552_2.nsv", "result1552_3.nsv", "result1552_4.nsv", "result1552_5.nsv", "result1552_6.nsv", "result1552_7.nsv", "result1552_8.nsv", "result1552_9.nsv", "result1552_10.nsv", "result1552_11.nsv", "result1552_12.nsv", "result1552_13.nsv", "result1552_14.nsv", "result1552_15.nsv", "result1552_16.nsv", "result1552_17.nsv", "result1552_18.nsv", "result1552_19.nsv"];
val thyn = "vfmTestDefs1552";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
