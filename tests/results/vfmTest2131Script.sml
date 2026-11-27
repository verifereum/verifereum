Theory vfmTest2131[no_sig_docs]
Ancestors vfmTestDefs2131
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2131_0.nsv", "result2131_1.nsv", "result2131_2.nsv", "result2131_3.nsv", "result2131_4.nsv", "result2131_5.nsv", "result2131_6.nsv", "result2131_7.nsv"];
val thyn = "vfmTestDefs2131";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
