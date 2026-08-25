Theory vfmTest2606[no_sig_docs]
Ancestors vfmTestDefs2606
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2606_0.nsv", "result2606_1.nsv", "result2606_2.nsv", "result2606_3.nsv"];
val thyn = "vfmTestDefs2606";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
