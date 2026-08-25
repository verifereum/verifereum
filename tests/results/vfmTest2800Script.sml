Theory vfmTest2800[no_sig_docs]
Ancestors vfmTestDefs2800
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2800_0.nsv", "result2800_1.nsv", "result2800_2.nsv", "result2800_3.nsv"];
val thyn = "vfmTestDefs2800";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
