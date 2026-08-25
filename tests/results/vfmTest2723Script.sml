Theory vfmTest2723[no_sig_docs]
Ancestors vfmTestDefs2723
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2723_0.nsv", "result2723_1.nsv", "result2723_2.nsv", "result2723_3.nsv"];
val thyn = "vfmTestDefs2723";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
