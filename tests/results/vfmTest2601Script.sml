Theory vfmTest2601[no_sig_docs]
Ancestors vfmTestDefs2601
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2601_0.nsv", "result2601_1.nsv", "result2601_2.nsv", "result2601_3.nsv"];
val thyn = "vfmTestDefs2601";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
