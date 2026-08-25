Theory vfmTest2664[no_sig_docs]
Ancestors vfmTestDefs2664
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2664_0.nsv", "result2664_1.nsv", "result2664_2.nsv", "result2664_3.nsv"];
val thyn = "vfmTestDefs2664";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
