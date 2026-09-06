Theory vfmTest2346[no_sig_docs]
Ancestors vfmTestDefs2346
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2346_0.nsv", "result2346_1.nsv", "result2346_2.nsv", "result2346_3.nsv", "result2346_4.nsv", "result2346_5.nsv", "result2346_6.nsv", "result2346_7.nsv", "result2346_8.nsv"];
val thyn = "vfmTestDefs2346";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
