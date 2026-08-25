Theory vfmTest2646[no_sig_docs]
Ancestors vfmTestDefs2646
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2646_0.nsv", "result2646_1.nsv", "result2646_2.nsv", "result2646_3.nsv"];
val thyn = "vfmTestDefs2646";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
