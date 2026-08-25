Theory vfmTest2488[no_sig_docs]
Ancestors vfmTestDefs2488
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2488_0.nsv", "result2488_1.nsv"];
val thyn = "vfmTestDefs2488";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
