Theory vfmTest2248[no_sig_docs]
Ancestors vfmTestDefs2248
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2248_0.nsv", "result2248_1.nsv"];
val thyn = "vfmTestDefs2248";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
