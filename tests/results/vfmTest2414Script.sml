Theory vfmTest2414[no_sig_docs]
Ancestors vfmTestDefs2414
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2414_0.nsv", "result2414_1.nsv", "result2414_2.nsv", "result2414_3.nsv", "result2414_4.nsv", "result2414_5.nsv"];
val thyn = "vfmTestDefs2414";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
