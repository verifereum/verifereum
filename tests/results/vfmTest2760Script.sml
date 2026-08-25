Theory vfmTest2760[no_sig_docs]
Ancestors vfmTestDefs2760
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2760_0.nsv", "result2760_1.nsv", "result2760_2.nsv", "result2760_3.nsv"];
val thyn = "vfmTestDefs2760";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
