Theory vfmTest2207[no_sig_docs]
Ancestors vfmTestDefs2207
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2207_0.nsv", "result2207_1.nsv", "result2207_2.nsv", "result2207_3.nsv", "result2207_4.nsv", "result2207_5.nsv", "result2207_6.nsv", "result2207_7.nsv", "result2207_8.nsv", "result2207_9.nsv", "result2207_10.nsv", "result2207_11.nsv", "result2207_12.nsv", "result2207_13.nsv", "result2207_14.nsv", "result2207_15.nsv", "result2207_16.nsv"];
val thyn = "vfmTestDefs2207";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
