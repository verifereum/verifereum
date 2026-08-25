Theory vfmTest2834[no_sig_docs]
Ancestors vfmTestDefs2834
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2834_0.nsv", "result2834_1.nsv", "result2834_2.nsv", "result2834_3.nsv"];
val thyn = "vfmTestDefs2834";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
