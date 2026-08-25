Theory vfmTest2701[no_sig_docs]
Ancestors vfmTestDefs2701
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2701_0.nsv", "result2701_1.nsv", "result2701_2.nsv", "result2701_3.nsv"];
val thyn = "vfmTestDefs2701";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
