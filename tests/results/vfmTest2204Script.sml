Theory vfmTest2204[no_sig_docs]
Ancestors vfmTestDefs2204
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2204_0.nsv", "result2204_1.nsv", "result2204_2.nsv", "result2204_3.nsv"];
val thyn = "vfmTestDefs2204";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
