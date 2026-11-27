Theory vfmTest1856[no_sig_docs]
Ancestors vfmTestDefs1856
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1856_0.nsv", "result1856_1.nsv", "result1856_2.nsv", "result1856_3.nsv", "result1856_4.nsv", "result1856_5.nsv", "result1856_6.nsv", "result1856_7.nsv", "result1856_8.nsv", "result1856_9.nsv"];
val thyn = "vfmTestDefs1856";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
