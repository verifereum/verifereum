Theory vfmTest2240[no_sig_docs]
Ancestors vfmTestDefs2240
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2240_0.nsv", "result2240_1.nsv", "result2240_2.nsv", "result2240_3.nsv", "result2240_4.nsv", "result2240_5.nsv", "result2240_6.nsv", "result2240_7.nsv", "result2240_8.nsv", "result2240_9.nsv"];
val thyn = "vfmTestDefs2240";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
