Theory vfmTest2945[no_sig_docs]
Ancestors vfmTestDefs2945
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2945_0.nsv", "result2945_1.nsv", "result2945_2.nsv", "result2945_3.nsv"];
val thyn = "vfmTestDefs2945";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
