Theory vfmTest2637[no_sig_docs]
Ancestors vfmTestDefs2637
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2637_0.nsv", "result2637_1.nsv", "result2637_2.nsv", "result2637_3.nsv"];
val thyn = "vfmTestDefs2637";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
