Theory vfmTest2961[no_sig_docs]
Ancestors vfmTestDefs2961
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2961_0.nsv", "result2961_1.nsv", "result2961_2.nsv"];
val thyn = "vfmTestDefs2961";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
