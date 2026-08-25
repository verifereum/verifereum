Theory vfmTest2608[no_sig_docs]
Ancestors vfmTestDefs2608
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2608_0.nsv", "result2608_1.nsv", "result2608_2.nsv", "result2608_3.nsv"];
val thyn = "vfmTestDefs2608";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
