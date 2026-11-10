Theory vfmTest2691[no_sig_docs]
Ancestors vfmTestDefs2691
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2691_0.nsv", "result2691_1.nsv", "result2691_2.nsv", "result2691_3.nsv", "result2691_4.nsv", "result2691_5.nsv", "result2691_6.nsv", "result2691_7.nsv", "result2691_8.nsv", "result2691_9.nsv"];
val thyn = "vfmTestDefs2691";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
