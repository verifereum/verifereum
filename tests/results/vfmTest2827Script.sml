Theory vfmTest2827[no_sig_docs]
Ancestors vfmTestDefs2827
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2827_0.nsv", "result2827_1.nsv", "result2827_2.nsv", "result2827_3.nsv"];
val thyn = "vfmTestDefs2827";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
