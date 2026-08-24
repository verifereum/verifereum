Theory vfmTest2747[no_sig_docs]
Ancestors vfmTestDefs2747
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2747_0.nsv", "result2747_1.nsv", "result2747_2.nsv", "result2747_3.nsv"];
val thyn = "vfmTestDefs2747";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
