Theory vfmTest2367[no_sig_docs]
Ancestors vfmTestDefs2367
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2367_0.nsv", "result2367_1.nsv", "result2367_2.nsv", "result2367_3.nsv"];
val thyn = "vfmTestDefs2367";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
