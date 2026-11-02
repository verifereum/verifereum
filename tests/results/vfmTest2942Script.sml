Theory vfmTest2942[no_sig_docs]
Ancestors vfmTestDefs2942
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2942_0.nsv", "result2942_1.nsv", "result2942_2.nsv", "result2942_3.nsv", "result2942_4.nsv"];
val thyn = "vfmTestDefs2942";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
