Theory vfmTest2742[no_sig_docs]
Ancestors vfmTestDefs2742
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2742_0.nsv", "result2742_1.nsv", "result2742_2.nsv", "result2742_3.nsv"];
val thyn = "vfmTestDefs2742";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
