Theory vfmTest2943[no_sig_docs]
Ancestors vfmTestDefs2943
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2943_0.nsv", "result2943_1.nsv", "result2943_2.nsv", "result2943_3.nsv", "result2943_4.nsv", "result2943_5.nsv", "result2943_6.nsv", "result2943_7.nsv", "result2943_8.nsv", "result2943_9.nsv", "result2943_10.nsv", "result2943_11.nsv"];
val thyn = "vfmTestDefs2943";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
