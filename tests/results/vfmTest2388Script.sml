Theory vfmTest2388[no_sig_docs]
Ancestors vfmTestDefs2388
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2388_0.nsv", "result2388_1.nsv"];
val thyn = "vfmTestDefs2388";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
